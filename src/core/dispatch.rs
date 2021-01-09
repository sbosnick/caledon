// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The bridge between the [Wayland] wire protocol and its higher level
//! protocol for incoming [`Message`]'s.
//!
//! The [`dispatcher`] consumes a [`Stream`] of [`Message`]'s and resolves when
//! the [`Stream`] is finished. It will dispatach each [`Message`] to a [`Target`]
//! in the provided [`TargetStore`] and will update the [`TargetStore`] depending
//! on the [`DispatchResult`].
//!
//! [Wayland]: https://wayland.freedesktop.org/
//! [`Message`]: super::Message
//! [`Stream`]: futures_core::Stream

use std::{future::Future, sync::Arc};

use futures_core::TryStream;
use futures_util::TryStreamExt as _;

/// Dispatches a [`Stream`] of incoming [`Message`]'s to the [`Target`]'s in a
/// [`TargetStore`].
///
/// `dispatcher` will resolve when the [`Stream`] either returns an error or
/// ends. For each item in the [`Stream`] (which is intended to be a
/// [`Message`]) `dispatcher` will use `f` to extract the tag of the message
/// and then use that tag to look up the [`Target`] in the [`TargetStore`]. It
/// will dispatach the item to that [`Target`] and update the [`TargetStore`]
/// depending  on the [`DispatchResult`].
///
/// [`Message`]: super::Message
/// [`Stream`]: futures_core::Stream
// TODO: remove this when it is no longer needed
#[allow(dead_code)]
pub async fn dispatcher<ST, SI, F, G, T, TS>(stream: ST, f: F, targets: TS) -> Result<(), ST::Error>
where
    ST: TryStream<Ok = T>,
    SI: Target<T, G, Tag = TS::Tag>,
    TS: TargetStore<SI> + Clone,
    F: Fn(&T) -> TS::Tag,
    G: Future<Output = DispatchResult<TS::Tag, SI>>,
{
    let f = &f;

    stream
        .try_for_each(move |item| {
            let mut targets = targets.clone();

            async move {
                use DispatchResult::{Add, Continue, Remove};

                let target = targets.get(f(&item));

                match target.dispatch(item).await {
                    Add(tag, new_target) => {
                        targets.add(tag, new_target);
                    }
                    Remove(tag) => {
                        targets.remove(tag);
                    }
                    Continue => {}
                }

                Ok(())
            }
        })
        .await
}

/// Interface for the dispatch target of the [`dispatcher`].
pub trait Target<T, F>: Sized
where
    F: Future<Output = DispatchResult<Self::Tag, Self>>,
{
    type Tag;

    fn dispatch(&self, item: T) -> F;
}

/// The result of a [`dispatch`] operation.
///
/// [`dispatcher`] will use this result to update its [`TargetStore`].
///
/// [`dispatch`]: Target::dispatch
#[derive(Debug, Clone)]
pub enum DispatchResult<Tag, SI> {
    Add(Tag, SI),
    Remove(Tag),
    Continue,
}

/// Interface for the storage of the live dispatch [`Target`]'s for
/// [`dispatcher`].
pub trait TargetStore<SI> {
    type Tag;

    fn get(&self, tag: Self::Tag) -> Arc<SI>;
    fn add(&mut self, tag: Self::Tag, target: SI);
    fn remove(&mut self, tag: Self::Tag);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{store::ObjectMap, ObjectId, ServerRole};

    use std::{
        iter,
        sync::{Arc, Mutex},
    };

    use futures::{future::ready, future::Ready, stream};

    #[derive(Debug, Clone)]
    struct FakeTarget {
        item: Arc<Mutex<Option<u8>>>,
        result: Box<DispatchResult<ObjectId, FakeTarget>>,
    }

    impl FakeTarget {
        fn new(item: Arc<Mutex<Option<u8>>>, result: DispatchResult<ObjectId, Self>) -> Self {
            Self {
                item,
                result: Box::new(result),
            }
        }
    }

    impl Target<u8, Ready<DispatchResult<ObjectId, Self>>> for FakeTarget {
        type Tag = ObjectId;

        fn dispatch(&self, item: u8) -> Ready<DispatchResult<Self::Tag, Self>> {
            let mut guard = self.item.lock().expect("Can't lock mutex");
            *guard = Some(item);
            ready(*self.result.clone())
        }
    }

    #[tokio::test]
    async fn dispatcher_dispatches_default_tag_to_default_target() {
        let tag = ObjectId(0);
        let item = 1;
        let result: Result<_, ()> = Ok(item);
        let stream = stream::iter(iter::once(result));
        let inner = Arc::new(Mutex::new(None));
        let target = FakeTarget::new(inner.clone(), DispatchResult::Continue);
        let targets = ObjectMap::new(tag, target, ServerRole {});

        let _ = dispatcher(stream, |_| tag, targets).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_unknown_tag_to_default_target() {
        let tag1 = ObjectId(1);
        let tag0 = ObjectId(0);
        let item = 1;
        let result: Result<_, ()> = Ok(item);
        let stream = stream::iter(iter::once(result));
        let inner = Arc::new(Mutex::new(None));
        let target = FakeTarget::new(inner.clone(), DispatchResult::Continue);
        let targets = ObjectMap::new(tag1, target, ServerRole {});

        let _ = dispatcher(stream, |_| tag0, targets).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_too_big_tag_to_default_target() {
        let tag0 = ObjectId(0);
        let tag1 = ObjectId(1);
        let item = 1;
        let result: Result<_, ()> = Ok(item);
        let stream = stream::iter(iter::once(result));
        let inner = Arc::new(Mutex::new(None));
        let target = FakeTarget::new(inner.clone(), DispatchResult::Continue);
        let targets = ObjectMap::new(tag0, target, ServerRole {});

        let _ = dispatcher(stream, |_| tag1, targets).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_empty_stream() {
        let tag = ObjectId(0);
        let stream = stream::empty::<Result<u8, ()>>();
        let target = FakeTarget::new(Arc::new(Mutex::new(None)), DispatchResult::Continue);
        let targets = ObjectMap::new(tag, target, ServerRole {});

        let _ = dispatcher(stream, |_| tag, targets).await;
    }

    #[tokio::test]
    async fn dispatcher_dispatches_to_added_target() {
        let tag0 = ObjectId(0);
        let tag1 = ObjectId(1);
        let item = 1;
        let result: Result<u8, ()> = Ok(item);
        let stream = stream::iter(vec![Ok(0), result]);
        let inner = Arc::new(Mutex::new(None));
        let target1 = FakeTarget::new(inner.clone(), DispatchResult::Continue);
        let target0 = FakeTarget::new(
            Arc::new(Mutex::new(None)),
            DispatchResult::Add(tag1, target1),
        );
        let targets = ObjectMap::new(tag0, target0, ServerRole {});

        let _ = dispatcher(stream, |tag| ObjectId(*tag as u32), targets).await;

        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }

    #[tokio::test]
    async fn dispatcher_dispatches_removed_target_to_default_target() {
        let tag0 = ObjectId(0);
        let tag1 = ObjectId(1);
        let item = 1;
        let result: Result<u8, ()> = Ok(item);
        let stream = stream::iter(vec![Ok(0), Ok(1), result]);
        let inner = Arc::new(Mutex::new(None));
        let target1 = FakeTarget::new(Arc::new(Mutex::new(None)), DispatchResult::Remove(tag1));
        let target0 = FakeTarget::new(inner.clone(), DispatchResult::Add(tag1, target1));
        let targets = ObjectMap::new(tag0, target0, ServerRole {});

        let _ = dispatcher(stream, |tag| ObjectId(*tag as u32), targets).await;
        let outcome = inner.lock().expect("Can't lock mutex");
        assert_eq!(*outcome, Some(item));
    }
}
