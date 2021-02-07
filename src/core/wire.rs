// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The top-level types and function for the [Wayland] wire protocol.
//!
//! [Wayland]: https://wayland.freedesktop.org/

use std::marker::PhantomData;

use futures_core::Stream;
use futures_sink::Sink;
use futures_util::stream::StreamExt;

use crate::IoChannel;

use super::{
    role::{ClientRole, HasFd, Role, SendMsg, ServerRole},
    store::ObjectMap,
    transport::WaylandTransport,
    ProtocolFamily,
};

/// Create the [Wayland] wire protocol sender, receiver, and state for
/// the given channel.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) fn make_wire_protocol<R, PF>(
    channel: impl IoChannel + Unpin,
) -> (WireSend<R, PF>, WireRecv<R, PF>, WireState<R, PF>)
where
    PF: ProtocolFamily + HasFd<R> + SendMsg<R>,
    R: Role,
{
    let map = ObjectMap::<PF, R>::new();
    let transport = WaylandTransport::<_, R, PF, _>::new(channel, map);
    let (_stream, _sink) = transport.split();

    (
        WireSend::<R, PF> {
            _phantom: PhantomData,
        },
        WireRecv::<R, PF> {
            _phantom: PhantomData,
        },
        WireState::<R, PF> {
            _phantom: PhantomData,
        },
    )
}

/// Interface for the operations to manipulate the [Wayland] wire protocol state.
///
/// The [Wayland] object-level protocol informs the wire-level protocol of state changes through
/// this interface.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) trait WaylandState<PF> {}

/// Errors in the operation of the [Wayland] wire protocol.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) enum WireError {}

/// The concrete implementation of [WaylandState] for the wire protocol.
pub(crate) struct WireState<R, PF> {
    _phantom: PhantomData<(R, PF)>,
}

impl<R, PF> WaylandState<PF> for WireState<R, PF> {}

/// The send half of the [Wayland] wire protocol.
///
/// A `WireSend` allows sending Wayland messages accross the wire-protocol wrapped channel. The
/// type of messages that can be sent depend on the role (the `R` type parameter). It can send
/// `PF::Requests` for the `ClientRole` and `PF::Events` for the `ServerRole`.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) struct WireSend<R, PF> {
    _phantom: PhantomData<(R, PF)>,
}

impl<PF: ProtocolFamily> Sink<PF::Requests> for WireSend<ClientRole, PF> {
    type Error = WireError;

    fn poll_ready(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        todo!()
    }

    fn start_send(self: std::pin::Pin<&mut Self>, _item: PF::Requests) -> Result<(), Self::Error> {
        todo!()
    }

    fn poll_flush(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        todo!()
    }

    fn poll_close(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        todo!()
    }
}

impl<PF: ProtocolFamily> Sink<PF::Events> for WireSend<ServerRole, PF> {
    type Error = WireError;

    fn poll_ready(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        todo!()
    }

    fn start_send(self: std::pin::Pin<&mut Self>, _item: PF::Events) -> Result<(), Self::Error> {
        todo!()
    }

    fn poll_flush(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        todo!()
    }

    fn poll_close(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        todo!()
    }
}

/// The receive half of the [Wayland] wire protocol.
///
/// A `WireRecv` allows receiving Wayland messages from the wire-protocol wrapped channel. The type
/// of messages that can be received depends on the role (the `R` type parameter).  It can receive
/// `PF::Events` for the `ClientRole` and `PF::Requests` for the `ServerRole`.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) struct WireRecv<R, PF> {
    _phantom: PhantomData<(R, PF)>,
}

impl<PF: ProtocolFamily> Stream for WireRecv<ClientRole, PF> {
    type Item = Result<<PF as ProtocolFamily>::Events, WireError>;

    fn poll_next(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        todo!()
    }
}

impl<PF: ProtocolFamily> Stream for WireRecv<ServerRole, PF> {
    type Item = Result<<PF as ProtocolFamily>::Requests, WireError>;

    fn poll_next(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        todo!()
    }
}
