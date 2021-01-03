// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::{
    convert::TryInto,
    sync::{Arc, Mutex},
};

use crate::core::{dispatch::TargetStore, ObjectId};

#[derive(Debug)]
pub struct ObjectMap<SI> {
    shared: Arc<Shared<SI>>,
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

impl<SI> ObjectMap<SI> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn new(ObjectId(default_tag): ObjectId, default: SI) -> Self {
        let default_tag = default_tag.try_into().unwrap();
        let mut inner = Vec::with_capacity(default_tag + 1);
        inner.resize_with(default_tag, || None);
        inner.push(Some(Arc::new(default)));

        Self {
            shared: Arc::new(Shared {
                state: Mutex::new(State { inner, default_tag }),
            }),
        }
    }
}

impl<SI> TargetStore<SI> for ObjectMap<SI> {
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

impl<SI> Clone for ObjectMap<SI> {
    fn clone(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }
}
