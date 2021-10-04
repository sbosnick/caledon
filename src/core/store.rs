// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The storage for the the live protocol objects.
//!
//! An [`ObjectMap`] provides a means for the [`wire`] module to track the live protocol objects
//! for the purpose of dispatching an incoming [`Message`]. It also exposes this information to the
//! [`transport`] module through its implementation of [`MessageFdMap`].
//!
//!
//! [`transport`]: super::transport
//! [`wire`]: super::wire
//! [`Message`]: super::Message

use std::{
    convert::TryInto,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
    sync::{Arc, Mutex},
};

use snafu::{ensure, Snafu};
use vob::Vob;

use super::{
    role::{HasFd, Role, ServerRole},
    transport::MessageFdMap,
    ClientRole, ObjectId,
};

/// A concurancy safe map from an [`ObjectId`] to a live protocol object.
#[derive(Debug)]
pub(crate) struct ObjectMap<SI, R> {
    shared: Arc<Shared<SI, R>>,
}

#[derive(Debug)]
struct Shared<SI, R> {
    source: Mutex<IdSource<R>>,
    map: Mutex<Map<SI>>,
}

#[derive(Debug)]
struct Map<SI> {
    // client created objects
    client: Vec<Option<Arc<SI>>>,

    // server created objects
    server: Vec<Option<Arc<SI>>>,
}

#[derive(Debug)]
struct IdSource<R, E = Extractor> {
    pool: Vob,
    _phantom: PhantomData<(R, E)>,
}

#[derive(Debug, Snafu)]
#[snafu(display("Exhasted the pool of available object id's"))]
pub(crate) struct ObjectIdExhastedError;

impl<SI, R> ObjectMap<SI, R>
where
    R: Role,
    Extractor: ExtractIndex<R>,
{
    pub fn new() -> Self {
        Self {
            shared: Arc::new(Shared {
                source: Mutex::new(IdSource::default()),
                map: Mutex::new(Map::default()),
            }),
        }
    }

    pub fn get(&self, object_id: ObjectId) -> Option<Arc<SI>> {
        if object_id.is_null() {
            None
        } else {
            let state = self.shared.map.lock().unwrap();
            let tag = get_tag(object_id);

            if !state.is_valid_idx(tag) {
                None
            } else {
                state[tag].clone()
            }
        }
    }

    pub fn create(&self, f: impl Fn(ObjectId) -> SI) -> Result<Arc<SI>, ObjectIdExhastedError> {
        let new_id = {
            let mut source = self.shared.source.lock().unwrap();
            source.allocate_id()?
        };

        let new_obj = Arc::new(f(new_id));

        {
            let mut map = self.shared.map.lock().unwrap();
            let tag = get_tag(new_id);
            map.ensure_idx(tag);
            map[tag] = Some(new_obj.clone());
        }
        Ok(new_obj)
    }

    pub fn add(&self, id: ObjectId, object: SI) {
        assert!(
            !Extractor::is_local_object_id(id),
            "Attempt to add a local object id to to the ObjectMap."
        );

        let mut map = self.shared.map.lock().unwrap();
        let tag = get_tag(id);
        map.ensure_idx(tag);
        map[tag] = Some(Arc::new(object));
    }

    pub fn remove(&self, id: ObjectId) {
        {
            let mut map = self.shared.map.lock().unwrap();
            let tag = get_tag(id);
            map[tag] = None;
        }

        if Extractor::is_local_object_id(id) {
            let mut source = self.shared.source.lock().unwrap();
            source.release_id(id);
        }
    }
}

fn get_tag(ObjectId(tag): ObjectId) -> NonZeroUsize {
    NonZeroUsize::new(tag.try_into().unwrap()).expect("Invalid object ID passed to ObjectMap.")
}

impl<SI, R> MessageFdMap for ObjectMap<SI, R>
where
    R: Role,
    SI: HasFd<R>,
{
    fn message_has_fd(&self, ObjectId(tag): ObjectId, opcode: u16) -> bool {
        let state = self.shared.map.lock().unwrap();
        let tag = match NonZeroUsize::new(tag.try_into().unwrap()) {
            Some(tag) => tag,
            None => return false,
        };

        if !state.is_valid_idx(tag) {
            return false;
        }

        state[tag]
            .as_ref()
            .map_or(false, |target| target.has_fd(opcode))
    }
}

impl<SI, R> Clone for ObjectMap<SI, R> {
    fn clone(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }
}

const CLIENT_ID_BASE: usize = 0x00000001;
const SERVER_ID_BASE: usize = 0xff000000;
const SERVER_ID_MAX: usize = 0xffffffff;

impl<SI> Map<SI> {
    fn get_vec_idx(&self, index: NonZeroUsize) -> (&Vec<Option<Arc<SI>>>, usize) {
        let idx: usize = index.into();
        if idx < SERVER_ID_BASE {
            (&self.client, idx - CLIENT_ID_BASE)
        } else {
            (&self.server, idx - SERVER_ID_BASE)
        }
    }

    fn get_vec_idx_mut(&mut self, index: NonZeroUsize) -> (&mut Vec<Option<Arc<SI>>>, usize) {
        let idx: usize = index.into();
        if idx < SERVER_ID_BASE {
            (&mut self.client, idx - CLIENT_ID_BASE)
        } else {
            (&mut self.server, idx - SERVER_ID_BASE)
        }
    }

    fn ensure_idx(&mut self, index: NonZeroUsize) {
        let (vector, idx) = self.get_vec_idx_mut(index);

        if vector.len() <= idx {
            vector.resize_with(idx + 1, || None);
        }
    }

    fn is_valid_idx(&self, index: NonZeroUsize) -> bool {
        let (vector, idx) = self.get_vec_idx(index);

        idx < vector.len()
    }
}

impl<SI> Index<NonZeroUsize> for Map<SI> {
    type Output = Option<Arc<SI>>;

    fn index(&self, index: NonZeroUsize) -> &Self::Output {
        let (vector, idx) = self.get_vec_idx(index);

        &vector[idx]
    }
}

impl<SI> IndexMut<NonZeroUsize> for Map<SI> {
    fn index_mut(&mut self, index: NonZeroUsize) -> &mut Self::Output {
        let (vector, idx) = self.get_vec_idx_mut(index);

        &mut vector[idx]
    }
}

impl<SI> Default for Map<SI> {
    fn default() -> Self {
        Self {
            client: Vec::new(),
            server: Vec::new(),
        }
    }
}

impl<R: Role, E: ExtractIndex<R>> IdSource<R, E> {
    fn allocate_id(&mut self) -> Result<ObjectId, ObjectIdExhastedError> {
        match self.pool.iter_unset_bits(..).next() {
            Some(idx) => {
                self.pool.set(idx, true);
                E::make_object_id(idx)
            }
            None => {
                self.pool.push(true);
                E::make_object_id(self.pool.len() - 1)
            }
        }
    }

    fn release_id(&mut self, id: ObjectId) {
        self.pool.set(E::from_object_id(id), false);
    }
}

impl<R: Role> Default for IdSource<R, Extractor> {
    fn default() -> Self {
        Self {
            pool: Vob::new(),
            _phantom: PhantomData,
        }
    }
}

pub(crate) trait ExtractIndex<R: Role> {
    fn is_local_object_id(id: ObjectId) -> bool;
    fn from_object_id(id: ObjectId) -> usize;
    fn make_object_id(index: usize) -> Result<ObjectId, ObjectIdExhastedError>;
}

#[derive(Debug)]
pub(crate) struct Extractor;

impl ExtractIndex<ServerRole> for Extractor {
    fn from_object_id(ObjectId(id): ObjectId) -> usize {
        assert!(id as usize >= SERVER_ID_BASE);
        id as usize - SERVER_ID_BASE
    }

    fn make_object_id(index: usize) -> Result<ObjectId, ObjectIdExhastedError> {
        ensure!(
            index < SERVER_ID_MAX - SERVER_ID_BASE,
            ObjectIdExhastedContext {}
        );
        Ok(ObjectId((index + SERVER_ID_BASE) as u32))
    }

    fn is_local_object_id(ObjectId(id): ObjectId) -> bool {
        let id: usize = id.try_into().unwrap();
        SERVER_ID_BASE <= id && id <= SERVER_ID_MAX
    }
}

impl ExtractIndex<ClientRole> for Extractor {
    fn from_object_id(ObjectId(id): ObjectId) -> usize {
        assert!(id != 0 && (id as usize) < SERVER_ID_BASE);
        id as usize - CLIENT_ID_BASE
    }

    fn make_object_id(index: usize) -> Result<ObjectId, ObjectIdExhastedError> {
        ensure!(
            index < ((SERVER_ID_BASE - 1) - CLIENT_ID_BASE),
            ObjectIdExhastedContext {}
        );
        Ok(ObjectId((index + CLIENT_ID_BASE) as u32))
    }

    fn is_local_object_id(ObjectId(id): ObjectId) -> bool {
        let id: usize = id.try_into().unwrap();
        CLIENT_ID_BASE <= id && id < SERVER_ID_BASE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vob::vob;

    use crate::core::{
        role::{ClientRole, ServerRole},
        testutil::{BuildTimeWaylandTests, FdPasser, Protocols},
    };

    #[test]
    fn object_map_has_fd_for_fd_event() {
        let tag = ObjectId(1);
        let object = Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(FdPasser {}));

        let sut = ObjectMap::<Protocols, ServerRole>::new();
        sut.add(tag, object);
        let has_fd = sut.message_has_fd(tag, 1);

        assert!(
            has_fd,
            "The FdEvent for an FdPasser was did not have an fd."
        );
    }

    #[test]
    fn object_map_has_no_fd_for_destroy_request() {
        let tag = ObjectId(1);

        let sut = ObjectMap::<Protocols, ClientRole>::new();
        sut.create(|_| {
            Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(FdPasser {}))
        })
        .unwrap();
        let has_fd = sut.message_has_fd(tag, 0);

        assert!(
            !has_fd,
            "The DestroyRequest for an FdPasser was did have an fd."
        );
    }

    #[test]
    fn map_ensure_idx_increses_right_vec() {
        let index = NonZeroUsize::new(SERVER_ID_BASE + 3).unwrap();

        let mut sut = Map::<u8>::default();
        sut.ensure_idx(index);

        assert_eq!(sut.client.len(), 0);
        assert_eq!(sut.server.len(), 4);
    }

    #[test]
    fn map_index_writes_to_right_vec() {
        let index = NonZeroUsize::new(SERVER_ID_BASE + 3).unwrap();

        let mut sut = Map::<u8>::default();
        sut.ensure_idx(index);
        sut[index] = Some(Arc::new(5));

        assert!(sut.server[3].is_some());
    }

    #[test]
    fn client_id_source_allocates_id_1() {
        let mut sut = IdSource::<ClientRole>::default();
        let result = sut.allocate_id().unwrap();

        assert_eq!(result, ObjectId(1));
    }

    #[test]
    fn server_id_source_allocate_from_server_range() {
        let mut sut = IdSource::<ServerRole>::default();
        let result = sut.allocate_id().unwrap();

        assert_eq!(result, ObjectId(SERVER_ID_BASE as u32));
    }

    #[test]
    fn id_source_reuses_released_id() {
        let mut sut = IdSource::<ServerRole>::default();
        let id1 = sut.allocate_id().unwrap();
        sut.release_id(id1);
        let id2 = sut.allocate_id().unwrap();

        assert_eq!(id1, id2);
    }

    #[test]
    fn id_source_allocates_densely() {
        let mut sut = IdSource::<ServerRole>::default();
        let _ = sut.allocate_id();
        let id = sut.allocate_id().unwrap();
        sut.release_id(id);
        let _ = sut.allocate_id();
        let _ = sut.allocate_id();

        assert_eq!(sut.pool.len(), 3);
    }

    #[test]
    fn full_server_id_source_allocate_is_error() {
        let pool = vob![SERVER_ID_MAX - SERVER_ID_BASE; true];

        let mut sut = IdSource::<ServerRole> {
            pool,
            _phantom: PhantomData,
        };
        let result = sut.allocate_id();

        assert!(result.is_err());
    }

    #[test]
    fn full_client_id_source_allocate_is_error() {
        let pool = vob![(SERVER_ID_BASE - 1) - CLIENT_ID_BASE; true];

        let mut sut = IdSource::<ClientRole> {
            pool,
            _phantom: PhantomData,
        };
        let result = sut.allocate_id();

        assert!(result.is_err());
    }
}
