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
    sync::{Arc, Mutex},
};

use super::{dispatch::TargetStore, transport::MessageFdMap, HasFd, ObjectId, Role};

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
    inner: Vec<Option<Arc<SI>>>,
    default_tag: usize,
}

impl<SI, R> ObjectMap<SI, R>
where
    R: Role,
{
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn new(ObjectId(default_tag): ObjectId, default: SI, _role: R) -> Self {
        let default_tag = default_tag.try_into().unwrap();
        let mut inner = Vec::with_capacity(default_tag + 1);
        inner.resize_with(default_tag, || None);
        inner.push(Some(Arc::new(default)));

        Self {
            shared: Arc::new(Shared {
                state: Mutex::new(State { inner, default_tag }),
            }),
            _phantom: PhantomData,
        }
    }
}

impl<SI, R> TargetStore<SI> for ObjectMap<SI, R> {
    type Tag = ObjectId;

    fn get(&self, ObjectId(tag): ObjectId) -> Arc<SI> {
        let state = self.shared.state.lock().unwrap();
        let tag: usize = tag.try_into().unwrap();

        match state.inner.get(tag) {
            Some(Some(target)) => target.clone(),
            Some(None) | None => state.inner[state.default_tag]
                .as_ref()
                .expect("default target not at default_tag")
                .clone(),
        }
    }

    fn add(&mut self, ObjectId(tag): ObjectId, target: SI) {
        let mut state = self.shared.state.lock().unwrap();
        let tag: usize = tag.try_into().unwrap();

        assert_ne!(
            tag, state.default_tag,
            "Attempt to add new default target to TargetStore"
        );

        if state.inner.len() < tag + 1 {
            state.inner.resize_with(tag + 1, || None);
        }
        state.inner[tag] = Some(Arc::new(target));
    }

    fn remove(&mut self, ObjectId(tag): ObjectId) {
        let mut state = self.shared.state.lock().unwrap();
        let tag: usize = tag.try_into().unwrap();

        assert_ne!(
            tag, state.default_tag,
            "Attempt to remove default target from TargetStore"
        );

        state.inner[tag] = None;
    }
}

impl<SI, R> MessageFdMap for ObjectMap<SI, R>
where
    R: Role,
    SI: HasFd<R>,
{
    fn message_has_fd(&self, ObjectId(tag): ObjectId, opcode: u16) -> bool {
        let state = self.shared.state.lock().unwrap();
        let tag: usize = tag.try_into().unwrap();

        match state.inner.get(tag) {
            Some(Some(target)) => target.has_fd(opcode),
            Some(None) | None => false,
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::core::{
        testutil::{BuildTimeWaylandTests, FdPasser, Protocols},
        ClientRole, ServerRole,
    };

    #[test]
    fn object_map_has_fd_for_fd_event() {
        let tag = ObjectId(0);
        let object = Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(FdPasser {}));

        let sut = ObjectMap::new(tag, object, ServerRole {});
        let has_fd = sut.message_has_fd(tag, 1);

        assert!(
            has_fd,
            "The FdEvent for an FdPasser was did not have an fd."
        );
    }

    #[test]
    fn object_map_has_no_fd_for_destroy_request() {
        let tag = ObjectId(0);
        let object = Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(FdPasser {}));

        let sut = ObjectMap::new(tag, object, ClientRole {});
        let has_fd = sut.message_has_fd(tag, 0);

        assert!(
            !has_fd,
            "The DestroyRequest for an FdPasser was did have an fd."
        );
    }
}
