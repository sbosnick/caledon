// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The [`Registry`] of [`Global`] objects for the [Wayland] protocol.
//!
//! The [`Registry`] is a key-value store which (currently) maps from a `u32` numeric name to a
//! [`Global`] record with information about the global [Wayland] object. This is not a
//! representation of the `wl_registry` protocol object, but rather a type that can be used on
//! either the client-side or the server-side to implement `wl_registry`.
//!
//! [`Registry`] can produce change notification (of type [`GlobalChange`]) through the
//! [`Registry::changes`]
//! method. This method takes a [`CancellationToken`] which is uses to implement a somewhat brutal
//! form of back pressues: if the caller of [`Registry::changes`] can't keep up with the stream of changes
//! that results then both the changes subscription and the passed in [`CancellationToken`] will be
//! cancelled.
//!
//! [Wayland]: https://wayland.freedesktop.org/

use std::{
    collections::HashMap,
    convert::TryInto,
    ffi::CString,
    iter::FromIterator,
    ops::Index,
    sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard},
};

use futures_channel::mpsc::{channel, Sender};
use futures_core::Stream;
use tokio_util::sync::CancellationToken;

/// A record of a global [Wayland] object.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Global {
    pub(crate) interface: CString,
    pub(crate) version: u32,
}

pub(crate) type GlobalKv = (u32, Global);
// TODO: remove this when it is no longer needed
#[allow(dead_code)]
pub(crate) type GlobalKvRef<'a> = (&'a u32, &'a Global);

/// A change indicator for the [`Registry`] from which the change notification arises.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum GlobalChange {
    Add(u32, Global),
    Remove(u32),
}

/// A key-value map of [Wayland] global objects with change notifications.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug)]
pub(crate) struct Registry {
    shared: Arc<Shared>,
}

#[derive(Debug)]
pub(crate) struct RegistryLockMut<'a> {
    lock: RwLockWriteGuard<'a, State>,
}

#[derive(Debug)]
pub(crate) struct RegistryLockRef<'a> {
    lock: RwLockReadGuard<'a, State>,
}

#[derive(Debug)]
struct Shared {
    state: RwLock<State>,
}

#[derive(Debug)]
struct State {
    map: HashMap<u32, Global>,
    subscribers: Vec<Subscriber>,
    next_key: u32,
}

#[derive(Debug)]
struct Subscriber {
    dead: bool,
    cancel: CancellationToken,
    sender: Sender<GlobalChange>,
}

impl Registry {
    pub fn new() -> Registry {
        Registry {
            shared: Arc::new(Shared {
                state: RwLock::new(State::default()),
            }),
        }
    }

    /// Return a [`Stream`] of [`GlobalChange`] notifications.
    ///
    /// The supplied [`CancellationToken`] will be cancelled if the caller
    /// can't keep up with the generated steam of change notifications. This
    /// is a somewhat brutal form of back pressure.
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn changes(&self, cancel: CancellationToken) -> impl Stream<Item = GlobalChange> {
        let mut state = self.shared.state.write().unwrap();

        let (sender, reciever) = channel(CHANGE_CHANNEL_SIZE);
        state.subscribers.push(Subscriber {
            cancel,
            sender,
            dead: false,
        });

        reciever
    }

    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn lock_mut(&self) -> RegistryLockMut {
        RegistryLockMut {
            lock: self.shared.state.write().unwrap(),
        }
    }

    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn lock_ref(&self) -> RegistryLockRef {
        RegistryLockRef {
            lock: self.shared.state.read().unwrap(),
        }
    }
}

const CHANGE_CHANNEL_SIZE: usize = 64;

impl Default for Registry {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for Registry {
    fn clone(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }
}

impl FromIterator<Global> for Registry {
    fn from_iter<T: IntoIterator<Item = Global>>(iter: T) -> Self {
        iter.into_iter()
            .enumerate()
            .map(|(k, v)| {
                (
                    k.try_into()
                        .expect("Too many Global entires in the Registry"),
                    v,
                )
            })
            .collect()
    }
}

impl FromIterator<GlobalKv> for Registry {
    fn from_iter<T: IntoIterator<Item = (u32, Global)>>(iter: T) -> Self {
        Registry {
            shared: Arc::new(Shared {
                state: RwLock::new(State {
                    map: iter.into_iter().collect(),
                    ..Default::default()
                }),
            }),
        }
    }
}

impl Default for State {
    fn default() -> Self {
        State {
            next_key: 0,
            map: HashMap::new(),
            subscribers: Vec::new(),
        }
    }
}

impl<'a> RegistryLockMut<'a> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn add(&mut self, key: u32, value: Global) {
        self.lock.map.insert(key, value.clone());
        self.publish(GlobalChange::Add(key, value));
    }

    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn add_new(&mut self, value: Global) -> u32 {
        let key = self.lock.next_key;
        self.lock.next_key += 1;
        self.add(key, value);
        key
    }

    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn remove(&mut self, key: u32) {
        self.lock.map.remove(&key);
        self.publish(GlobalChange::Remove(key));
    }

    fn publish(&mut self, change: GlobalChange) {
        for subscriber in self.lock.subscribers.iter_mut() {
            if let Err(err) = subscriber.sender.try_send(change.clone()) {
                if !err.is_disconnected() {
                    // This is the brutal approach to back pressure: if you can't keep up then we
                    // will cancel both you and your subscription. This makes the assumption that
                    // the try_send error was because the channel was full.
                    subscriber.cancel.cancel();
                }
                subscriber.dead = true;
            }
        }

        self.lock.subscribers.retain(|s| !s.dead);
    }
}

impl<'a> Index<&u32> for RegistryLockRef<'a> {
    type Output = Global;

    fn index(&self, index: &u32) -> &Self::Output {
        &self.lock.map[index]
    }
}

impl<'a> RegistryLockRef<'a> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn iter(&self) -> impl Iterator<Item = GlobalKvRef> {
        self.lock.map.iter()
    }
}

impl Global {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    pub fn new(interface: CString, version: u32) -> Self {
        Self { interface, version }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_util::stream::StreamExt;

    #[test]
    fn registry_add_adds_global() {
        let interface = CString::new("wl_compositor").expect("bad CString");
        let global = Global::new(interface, 1);

        let sut = Registry::new();
        let key = sut.lock_mut().add_new(global.clone());
        let result = sut.lock_ref()[&key].clone();

        assert_eq!(result, global);
    }

    #[test]
    fn registry_iter_includes_added_global() {
        let interface = CString::new("wl_compositor").expect("bad CString");
        let global = Global::new(interface, 1);

        let sut = Registry::new();
        let key = sut.lock_mut().add_new(global.clone());
        let results: Vec<_> = sut
            .lock_ref()
            .iter()
            .map(|(name, global)| (*name, global.clone()))
            .collect();

        assert!(
            results.contains(&(key, global)),
            "Expected global not in the iteration."
        );
    }

    #[test]
    fn registry_from_iter_has_expected_globals() {
        let interface1 = CString::new("wl_compositor").expect("bad CString");
        let interface2 = CString::new("wl_subcompositor").expect("bad CString");
        let global1 = Global::new(interface1, 1);
        let global2 = Global::new(interface2, 2);
        let globals = vec![global1.clone(), global2];

        let sut = Registry::from_iter(globals);
        let result = sut.lock_ref()[&0].clone();

        assert_eq!(result, global1);
    }

    #[test]
    fn registry_changes_is_cancelled_if_not_drained() {
        let cancel = CancellationToken::new();
        let interface = CString::new("wl_compositor").expect("bad CString");
        let global = Global::new(interface, 1);

        let sut = Registry::new();
        let _not_polled = sut.changes(cancel.clone());
        let mut registry = sut.lock_mut();
        for _ in 0..(CHANGE_CHANNEL_SIZE / 2 + 1) {
            let key = registry.add_new(global.clone());
            registry.remove(key);
        }

        assert!(cancel.is_cancelled());
    }

    #[tokio::test]
    async fn registry_send_expected_change_event() {
        let interface = CString::new("wl_compositor").expect("bad CString");
        let version = 1;
        let global = Global::new(interface, version);
        let key = 1;

        let sut = Registry::new();
        let mut changes = sut.changes(CancellationToken::new());
        let handle = tokio::spawn(async move { changes.next().await.expect("empty changes") });
        sut.lock_mut().add(key, global.clone());
        let result = handle.await.expect("spawned task failed");

        assert_eq!(result, GlobalChange::Add(key, global));
    }
}
