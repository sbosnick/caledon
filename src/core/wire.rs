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

use std::{
    marker::PhantomData,
    pin::Pin,
    task::{Context, Poll},
};

use futures_core::Stream;
use futures_sink::Sink;
use futures_util::stream::{SplitStream, StreamExt};
use pin_project::pin_project;
use snafu::{OptionExt, ResultExt, Snafu};

use crate::IoChannel;

use super::{
    role::{ClientRole, HasFd, MakeMessage, RecvMsg, RecvMsgType, Role, SendMsg, ServerRole},
    store::ObjectMap,
    transport::{TransportError, WaylandTransport},
    ObjectId, OpCode, ProtocolFamily,
};

/// Create the [Wayland] wire protocol sender, receiver, and state for
/// the given channel.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) fn make_wire_protocol<T, R, PF>(
    channel: T,
) -> (WireSend<R, PF>, WireRecv<T, R, PF>, WireState<R, PF>)
where
    PF: ProtocolFamily + HasFd<R> + SendMsg<R>,
    R: Role,
    T: IoChannel + Unpin,
{
    let map = ObjectMap::<PF, R>::new();
    let transport = WaylandTransport::<_, R, PF, _>::new(channel, map.clone());
    let (_sink, stream) = transport.split();

    (
        WireSend::<R, PF> {
            _phantom: PhantomData,
        },
        WireRecv::<T, R, PF> { inner: stream, map },
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
#[derive(Debug, Snafu)]
pub(crate) enum WireError {
    #[snafu(display("Transport error when attempting to receive a message."))]
    RecvIoError { source: TransportError },

    #[snafu(display(
        "Received a message for object ID {} but that object does not exist.",
        object_id
    ))]
    RecvNoObject { object_id: ObjectId },

    #[snafu(display("Received a message with the opcode {} for object ID {} but that object does not have such a method.", opcode, object_id))]
    RecvNoMethod { object_id: ObjectId, opcode: OpCode },
}

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
#[pin_project]
pub(crate) struct WireRecv<T, R, PF> {
    #[pin]
    inner: SplitStream<WaylandTransport<T, R, PF, ObjectMap<PF, R>>>,
    map: ObjectMap<PF, R>,
}

impl<T, R, PF> Stream for WireRecv<T, R, PF>
where
    PF: ProtocolFamily
        + RecvMsg<R>
        + HasFd<R>
        + MakeMessage<R, Output = <PF as RecvMsg<R>>::Output>,
    R: Role,
    T: IoChannel + Unpin,
{
    type Item = Result<RecvMsgType<R, PF>, WireError>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let project = self.project();
        let mut inner = project.inner;
        let map = project.map;

        inner.as_mut().poll_next(cx).map(|opt| {
            opt.map(|res| {
                res.context(RecvIoError {}).and_then(|msg| {
                    let object_id = msg.object_id();
                    let opcode = msg.opcode();

                    map.get(object_id)
                        .context(RecvNoObject { object_id })
                        .and_then(|obj| {
                            obj.make_message(opcode, msg)
                                .context(RecvNoMethod { opcode, object_id })
                        })
                })
            })
        })
    }
}
