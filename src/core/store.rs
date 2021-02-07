// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The storage for the the live protocol objects.
//!
//! An [`ObjectMap`] bridges the [`transport`] and [`dispatch`] modules
//! with its implementations of [`MessageFdMap`] and [`TargetStore`]
//! respectively.
//!
//! [`transport`]: super::transport
//! [`dispatch`]: super::dispatch

use std::{
    convert::TryInto,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
    sync::{Arc, Mutex},
};

use super::{
    dispatch::TargetStore,
    role::{HasFd, Role},
    transport::MessageFdMap,
    ObjectId,
};

/// A concurancy safe map from an [`ObjectId`] to a live protocol object.
#[derive(Debug)]
pub(crate) struct ObjectMap<SI, R> {
    shared: Arc<Shared<SI>>,
    _phantom: PhantomData<R>,
}

#[derive(Debug)]
struct Shared<SI> {
    state: Mutex<State<SI>>,
}

#[derive(Debug)]
struct State<SI> {
    // client created objects
    client: Vec<Option<Arc<SI>>>,

    // server created objects
    server: Vec<Option<Arc<SI>>>,

    default_tag: Option<NonZeroUsize>,
}

impl<SI, R> ObjectMap<SI, R>
where
    R: Role,
{
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            shared: Arc::new(Shared {
                state: Mutex::new(State::default()),
            }),
            _phantom: PhantomData,
        }
    }

    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn set_default(&mut self, default_id: ObjectId, default: SI) {
        let mut state = self.shared.state.lock().unwrap();
        let tag = get_tag(default_id);
        state.set_default(tag, Arc::new(default));
    }
}

fn get_tag(ObjectId(tag): ObjectId) -> NonZeroUsize {
    NonZeroUsize::new(tag.try_into().unwrap()).expect("Invalid object ID passed to ObjectMap.")
}

impl<SI, R> TargetStore<SI> for ObjectMap<SI, R> {
    type Tag = ObjectId;

    fn get(&self, object_id: ObjectId) -> Arc<SI> {
        let state = self.shared.state.lock().unwrap();
        let tag = state.check_idx_or_default(get_tag(object_id));

        state[tag]
            .as_ref()
            .unwrap_or_else(|| {
                state[state.default_idx()]
                    .as_ref()
                    .expect("default target not at default_tag")
            })
            .clone()
    }

    fn add(&mut self, object_id: ObjectId, target: SI) {
        let mut state = self.shared.state.lock().unwrap();
        let tag = get_tag(object_id);

        assert_ne!(
            tag,
            state.default_idx(),
            "Attempt to add new default target to TargetStore"
        );

        state.ensure_idx(tag);
        state[tag] = Some(Arc::new(target));
    }

    fn remove(&mut self, object_id: ObjectId) {
        let mut state = self.shared.state.lock().unwrap();
        let tag = get_tag(object_id);

        assert_ne!(
            tag,
            state.default_idx(),
            "Attempt to remove default target from TargetStore"
        );

        if state.is_valid_idx(tag) {
            state[tag] = None;
        }
    }
}

impl<SI, R> MessageFdMap for ObjectMap<SI, R>
where
    R: Role,
    SI: HasFd<R>,
{
    fn message_has_fd(&self, ObjectId(tag): ObjectId, opcode: u16) -> bool {
        let state = self.shared.state.lock().unwrap();
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
            _phantom: PhantomData,
        }
    }
}

const CLIENT_ID_BASE: usize = 0x00000001;
const SERVER_ID_BASE: usize = 0xff000000;

impl<SI> State<SI> {
    fn default_idx(&self) -> NonZeroUsize {
        self.default_tag
            .expect("Attempt to use an ObjectMap before setting the default object.")
    }

    fn set_default(&mut self, index: NonZeroUsize, target: Arc<SI>) {
        self.ensure_idx(index);
        self[index] = Some(target);
        self.default_tag = Some(index);
    }

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

    fn check_idx_or_default(&self, index: NonZeroUsize) -> NonZeroUsize {
        if self.is_valid_idx(index) {
            index
        } else {
            self.default_idx()
        }
    }
}

impl<SI> Index<NonZeroUsize> for State<SI> {
    type Output = Option<Arc<SI>>;

    fn index(&self, index: NonZeroUsize) -> &Self::Output {
        let (vector, idx) = self.get_vec_idx(index);

        &vector[idx]
    }
}

impl<SI> IndexMut<NonZeroUsize> for State<SI> {
    fn index_mut(&mut self, index: NonZeroUsize) -> &mut Self::Output {
        let (vector, idx) = self.get_vec_idx_mut(index);

        &mut vector[idx]
    }
}

impl<SI> Default for State<SI> {
    fn default() -> Self {
        Self {
            client: Vec::new(),
            server: Vec::new(),
            default_tag: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::core::{
        role::{ClientRole, ServerRole},
        testutil::{BuildTimeWaylandTests, FdPasser, Protocols},
    };

    #[test]
    fn object_map_has_fd_for_fd_event() {
        let tag = ObjectId(1);
        let object = Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(FdPasser {}));

        let mut sut = ObjectMap::<_, ServerRole>::new();
        sut.set_default(tag, object);
        let has_fd = sut.message_has_fd(tag, 1);

        assert!(
            has_fd,
            "The FdEvent for an FdPasser was did not have an fd."
        );
    }

    #[test]
    fn object_map_has_no_fd_for_destroy_request() {
        let tag = ObjectId(1);
        let object = Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(FdPasser {}));

        let mut sut = ObjectMap::<_, ClientRole>::new();
        sut.set_default(tag, object);
        let has_fd = sut.message_has_fd(tag, 0);

        assert!(
            !has_fd,
            "The DestroyRequest for an FdPasser was did have an fd."
        );
    }

    #[test]
    fn state_ensure_idx_increses_right_vec() {
        let index = NonZeroUsize::new(SERVER_ID_BASE + 3).unwrap();

        let mut sut = State::<u8>::default();
        sut.ensure_idx(index);

        assert_eq!(sut.client.len(), 0);
        assert_eq!(sut.server.len(), 4);
    }

    #[test]
    fn state_check_idx_or_default_gets_default_if_vector_too_small() {
        let index = NonZeroUsize::new(SERVER_ID_BASE + 3).unwrap();
        let default_idx = NonZeroUsize::new(CLIENT_ID_BASE + 1).unwrap();

        let mut sut = State::<u8>::default();
        sut.set_default(default_idx, Arc::new(5));
        let result = sut.check_idx_or_default(index);

        assert_eq!(result, default_idx);
    }

    #[test]
    fn state_index_writes_to_right_vec() {
        let index = NonZeroUsize::new(SERVER_ID_BASE + 3).unwrap();

        let mut sut = State::<u8>::default();
        sut.ensure_idx(index);
        sut[index] = Some(Arc::new(5));

        assert!(sut.server[3].is_some());
    }
}
