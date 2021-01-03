// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::sync::{Arc, Mutex};

use crate::core::dispatch::TargetStore;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tag(usize);

impl Tag {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn new(tag: usize) -> Self {
        Self(tag)
    }

    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn into_usize(self) -> usize {
        self.0
    }
}

#[derive(Debug)]
pub struct TargetStoreImpl<SI> {
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

impl<SI> TargetStoreImpl<SI> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn new(Tag(default_tag): Tag, default: SI) -> Self {
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

impl<SI> TargetStore<SI> for TargetStoreImpl<SI> {
    type Tag = Tag;

    fn get(&self, Tag(tag): Tag) -> Arc<SI> {
        let state = self.shared.state.lock().unwrap();

        match state.inner.get(tag) {
            Some(Some(target)) => target.clone(),
            Some(None) | None => state.inner[state.default_tag]
                .as_ref()
                .expect("default target not at default_tag")
                .clone(),
        }
    }

    fn add(&mut self, Tag(tag): Tag, target: SI) {
        let mut state = self.shared.state.lock().unwrap();

        assert_ne!(
            tag, state.default_tag,
            "Attempt to add new default target to TargetStore"
        );

        if state.inner.len() < tag + 1 {
            state.inner.resize_with(tag + 1, || None);
        }
        state.inner[tag] = Some(Arc::new(target));
    }

    fn remove(&mut self, Tag(tag): Tag) {
        let mut state = self.shared.state.lock().unwrap();

        assert_ne!(
            tag, state.default_tag,
            "Attempt to remove default target from TargetStore"
        );

        state.inner[tag] = None;
    }
}

impl<SI> Clone for TargetStoreImpl<SI> {
    fn clone(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }
}
