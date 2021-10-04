// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use futures_channel::oneshot::{channel, Receiver, Sender};
use snafu::{OptionExt, Snafu};

use crate::core::ObjectId;

#[derive(Debug, Default)]
pub(crate) struct Callbacks {
    shared: Arc<Shared>,
}

#[derive(Debug, Default)]
struct Shared {
    state: Mutex<State>,
}

#[derive(Debug, Default)]
struct State {
    map: HashMap<ObjectId, Sender<u32>>,
}

#[derive(Debug, Snafu)]
#[snafu(display("Attempt to resolve an unknown wl_callback: {}.", id))]
pub(crate) struct UnknownCallbackError {
    id: ObjectId,
}

impl Callbacks {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add(&self, id: ObjectId) -> Receiver<u32> {
        let mut state = self.shared.state.lock().unwrap();
        let (sender, reciever) = channel();
        state.map.insert(id, sender);
        reciever
    }

    pub fn resolve(&self, id: ObjectId, result: u32) -> Result<(), UnknownCallbackError> {
        let mut state = self.shared.state.lock().unwrap();
        let sender = state
            .map
            .remove(&id)
            .context(UnknownCallbackContext { id })?;

        // If the send is Err that means that Receiver was dropped which
        // we treat as not being an error.
        let _ = sender.send(result);
        Ok(())
    }
}

impl Clone for Callbacks {
    fn clone(&self) -> Self {
        Callbacks {
            shared: self.shared.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::core::testutil::new_object_id;

    use super::*;

    #[test]
    fn callbacks_resolves_added_id_with_result() {
        let value = 5;
        let id = new_object_id(3);

        let sut = Callbacks::new();
        let mut recv = sut.add(id);
        sut.resolve(id, value).expect("resolved failed");
        let result = recv.try_recv().expect("resolve failue");

        assert_eq!(result, Some(value))
    }

    #[test]
    fn callbacks_resolve_unknown_id_is_error() {
        let id = new_object_id(3);

        let sut = Callbacks::new();
        let result = sut.resolve(id, 5);

        assert!(result.is_err());
    }

    #[test]
    fn callbacks_resolve_twice_is_error() {
        let id = new_object_id(3);

        let sut = Callbacks::new();
        let _recv = sut.add(id);
        sut.resolve(id, 5).expect("resolved failed");
        let result = sut.resolve(id, 6);

        assert!(result.is_err());
    }

    #[test]
    fn callbacks_resolved_for_dropped_recv_is_not_error() {
        let id = new_object_id(3);

        let sut = Callbacks::new();
        drop(sut.add(id));
        let result = sut.resolve(id, 6);

        assert!(result.is_ok());
    }
}
