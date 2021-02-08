// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The client side of the higher level [Wayland] object protocol.
//!
//! [Wayland]: https://wayland.freedesktop.org/

use std::marker::PhantomData;

use futures_core::Stream;
use futures_sink::Sink;
use snafu::Snafu;

use crate::{
    core::{
        make_wire_protocol, ClientRole, WaylandState, WireError, WireRecv, WireSend, WireState,
    },
    protocols, IoChannel,
};

/// The core client-side object to access a [Wayland] server.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub struct Display<T> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    inner: DisplayImpl<
        WireSend<ClientRole, protocols::Protocols>,
        WireRecv<T, ClientRole, protocols::Protocols>,
        WireState<ClientRole, protocols::Protocols>,
    >,
}

impl<T> Display<T>
where
    T: IoChannel + Unpin,
{
    /// Create a new `Display`.
    pub async fn new(channel: T) -> Result<Self, ClientError> {
        let (send, recv, state) = make_wire_protocol(channel);

        Ok(Display {
            inner: DisplayImpl::new(send, recv, state)?,
        })
    }

    /// Dispatch incoming event messages.
    ///
    /// This method resolves with either a fatal error on the channel or if the
    /// stream of event messages reaches the end.
    pub async fn dispatch(&self) -> Result<(), ClientError> {
        todo!();
    }
}

/// The possible errors arising in the core client-side [Wayland] objects.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug, Snafu)]
pub enum ClientError {}

struct DisplayImpl<Si, St, WS> {
    _phantom: PhantomData<(Si, St, WS)>,
}

impl<Si, St, WS> DisplayImpl<Si, St, WS>
where
    Si: Sink<protocols::Requests>,
    St: Stream<Item = Result<protocols::Events, WireError>>,
    WS: WaylandState<protocols::Protocols>,
{
    fn new(_send: Si, _recv: St, _state: WS) -> Result<Self, ClientError> {
        todo!()
    }
}
