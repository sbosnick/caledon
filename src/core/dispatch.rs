// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::future::Future;

use futures_core::TryStream;
use futures_util::TryStreamExt as _;

pub use store::Tag;
use store::TargetStore;

// TODO: remove this when it is no longer needed
#[allow(dead_code)]
pub async fn dispatcher<ST, SI, F, G, T, TI>(
    stream: ST,
    f: F,
    default_tag: Tag,
    default: SI,
    info: TI,
) -> Result<(), ST::Error>
where
    ST: TryStream<Ok = T>,
    SI: Target<T, G>,
    F: Fn(&T) -> Tag,
    G: Future<Output = DispatchResult<SI>>,
    TI: TargetInfo<SI> + Clone,
{
    let targets = TargetStore::new(default_tag, default);
    let f = &f;

    stream
        .try_for_each(move |item| {
            let mut targets = targets.clone();
            let mut info = info.clone();

            async move {
                use DispatchResult::{Add, Continue, Remove};

                let target = targets.get(f(&item));

                match target.dispatch(item).await {
                    Add(tag, new_target) => {
                        info.add(tag, &new_target);
                        targets.add(tag, new_target);
                    }
                    Remove(tag) => {
                        info.remove(tag);
                        targets.remove(tag);
                    }
                    Continue => {}
                }

                Ok(())
            }
        })
        .await
}

pub trait Target<T, F>: Sized
where
    F: Future<Output = DispatchResult<Self>>,
{
    fn dispatch(&self, item: T) -> F;
}

#[derive(Debug, Clone)]
pub enum DispatchResult<SI> {
    Add(Tag, SI),
    Remove(Tag),
    Continue,
}

pub trait TargetInfo<T> {
    fn add(&mut self, tag: Tag, target: &T);
    fn remove(&mut self, tag: Tag);
}

mod store {
    use std::sync::{Arc, Mutex};

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
    pub struct TargetStore<SI> {
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

    impl<SI> TargetStore<SI> {
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

        pub fn get(&self, Tag(tag): Tag) -> Arc<SI> {
            let state = self.shared.state.lock().unwrap();

            match state.inner.get(tag) {
                Some(Some(target)) => target.clone(),
                Some(None) | None => state.inner[state.default_tag]
                    .as_ref()
                    .expect("default target not at default_tag")
                    .clone(),
            }
        }

        pub fn add(&mut self, Tag(tag): Tag, target: SI) {
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

        pub fn remove(&mut self, Tag(tag): Tag) {
            let mut state = self.shared.state.lock().unwrap();

            assert_ne!(
                tag, state.default_tag,
                "Attempt to remove default target from TargetStore"
            );

            state.inner[tag] = None;
        }
    }

    impl<SI> Clone for TargetStore<SI> {
        fn clone(&self) -> Self {
            Self {
                shared: self.shared.clone(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{
        iter,
        sync::{Arc, Mutex},
    };

    use futures::{future::ready, future::Ready, stream};

    #[derive(Debug, Clone)]
    struct FakeTarget {
        item: Arc<Mutex<Option<u8>>>,
        result: Box<DispatchResult<FakeTarget>>,
    }

    impl FakeTarget {
        fn new(item: Arc<Mutex<Option<u8>>>, result: DispatchResult<Self>) -> Self {
            Self {
                item,
                result: Box::new(result),
            }
        }
    }

    #[derive(Clone)]
    struct StubInfo {}

    impl TargetInfo<FakeTarget> for StubInfo {
        fn add(&mut self, _: Tag, _: &FakeTarget) {}

        fn remove(&mut self, _: Tag) {}
    }

    impl Target<u8, Ready<DispatchResult<Self>>> for FakeTarget {
        fn dispatch(&self, item: u8) -> Ready<DispatchResult<Self>> {
            let mut guard = self.item.lock().expect("Can't lock mutex");
            *guard = Some(item);
            ready(*self.result.clone())
        }
    }

    #[tokio::test]
    async fn dispatcher_dispatches_default_tag_to_default_target() {
        let tag = Tag::new(0);
        let item = 1;
        let result: Result<_, ()> = Ok(item);
        let stream = stream::iter(iter::once(result));
        let inner = Arc::new(Mutex::new(None));
        let target = FakeTarget::new(inner.clone(), DispatchResult::Continue);

        let _ = dispatcher(stream, |_| tag, tag, target, StubInfo {}).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_unknown_tag_to_default_target() {
        let tag1 = Tag::new(1);
        let tag0 = Tag::new(0);
        let item = 1;
        let result: Result<_, ()> = Ok(item);
        let stream = stream::iter(iter::once(result));
        let inner = Arc::new(Mutex::new(None));
        let target = FakeTarget::new(inner.clone(), DispatchResult::Continue);

        let _ = dispatcher(stream, |_| tag0, tag1, target, StubInfo {}).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_too_big_tag_to_default_target() {
        let tag0 = Tag::new(0);
        let tag1 = Tag::new(1);
        let item = 1;
        let result: Result<_, ()> = Ok(item);
        let stream = stream::iter(iter::once(result));
        let inner = Arc::new(Mutex::new(None));
        let target = FakeTarget::new(inner.clone(), DispatchResult::Continue);

        let _ = dispatcher(stream, |_| tag1, tag0, target, StubInfo {}).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_empty_stream() {
        let tag = Tag::new(0);
        let stream = stream::empty::<Result<u8, ()>>();
        let target = FakeTarget::new(Arc::new(Mutex::new(None)), DispatchResult::Continue);

        let _ = dispatcher(stream, |_| tag, tag, target, StubInfo {}).await;
    }

    #[tokio::test]
    async fn dispatcher_dispatches_to_added_target() {
        let tag0 = Tag::new(0);
        let tag1 = Tag::new(1);
        let item = 1;
        let result: Result<u8, ()> = Ok(item);
        let stream = stream::iter(vec![Ok(0), result]);
        let inner = Arc::new(Mutex::new(None));
        let target1 = FakeTarget::new(inner.clone(), DispatchResult::Continue);
        let target0 = FakeTarget::new(
            Arc::new(Mutex::new(None)),
            DispatchResult::Add(tag1, target1),
        );

        let _ = dispatcher(
            stream,
            |tag| Tag::new(*tag as usize),
            tag0,
            target0,
            StubInfo {},
        )
        .await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_removed_target_to_default_target() {
        let tag0 = Tag::new(0);
        let tag1 = Tag::new(1);
        let item = 1;
        let result: Result<u8, ()> = Ok(item);
        let stream = stream::iter(vec![Ok(0), Ok(1), result]);
        let inner = Arc::new(Mutex::new(None));
        let target1 = FakeTarget::new(Arc::new(Mutex::new(None)), DispatchResult::Remove(tag1));
        let target0 = FakeTarget::new(inner.clone(), DispatchResult::Add(tag1, target1));

        let _ = dispatcher(
            stream,
            |tag| Tag::new(*tag as usize),
            tag0,
            target0,
            StubInfo {},
        )
        .await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }
}
