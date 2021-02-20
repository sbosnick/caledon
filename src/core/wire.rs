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
    fmt::Display,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
};

use futures_core::Stream;
use futures_sink::Sink;
use futures_util::stream::{SplitSink, SplitStream, StreamExt};
use pin_project::pin_project;
use snafu::{OptionExt, ResultExt, Snafu};

use crate::IoChannel;

use super::{
    role::{HasFd, MakeMessage, RecvMsg, RecvMsgType, Role, SendMsg, SendMsgType},
    store::{ExtractIndex, Extractor, ObjectIdExhastedError, ObjectMap},
    transport::{TransportError, WaylandTransport},
    FromOpcodeError, ObjectId, OpCode, ProtocolFamily,
};

/// The [Wayland] wire protocol is a triple of a sender, receiver, and the state for a given
/// [`Role`] (the generic type `R`), and [`ProtocolFamily`] (`PF`). It is instantiated on a given
/// [`IoChannel`] (`T`).
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) type WireProtocol<T, R, PF> = (WireSend<T, R, PF>, WireRecv<T, R, PF>, WireState<R, PF>);

/// Create the [Wayland] wire protocol sender, receiver, and state for
/// the given channel.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) fn make_wire_protocol<T, R, PF>(channel: T) -> WireProtocol<T, R, PF>
where
    PF: ProtocolFamily + HasFd<R> + SendMsg<R>,
    R: Role,
    T: IoChannel + Unpin,
    Extractor: ExtractIndex<R>,
{
    let map = ObjectMap::<PF, R>::new();
    let transport = WaylandTransport::<_, R, PF, _>::new(channel, map.clone());
    let (sink, stream) = transport.split();

    (
        WireSend::<T, R, PF> { inner: sink },
        WireRecv::<T, R, PF> {
            inner: stream,
            map: map.clone(),
        },
        WireState::<R, PF> { map },
    )
}

/// Interface for the operations to manipulate the [Wayland] wire protocol state.
///
/// The [Wayland] object-level protocol informs the wire-level protocol of state changes through
/// this interface.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub(crate) trait WaylandState<PF> {
    fn create_object(&self, f: impl Fn(ObjectId) -> PF) -> Result<Arc<PF>, WireError>;
    fn add_remote_object(&self, id: ObjectId, object: PF);
    fn remove_object(&self, id: ObjectId);
}

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
    RecvNoMethod {
        source: FromOpcodeError<TransportError>,
        object_id: ObjectId,
        opcode: OpCode,
    },

    #[snafu(display("Transport error when attempting to send a message: {}.", phase))]
    SendIoError {
        source: TransportError,
        phase: SendIoErrorPhase,
    },

    #[snafu(display("Can't create a new object becasue there are already too many objects."))]
    CreateObjectError { source: ObjectIdExhastedError },
}

#[derive(Debug)]
pub(crate) enum SendIoErrorPhase {
    Ready,
    StartSend,
    Flush,
    Close,
}

impl Display for SendIoErrorPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            SendIoErrorPhase::Ready => "getting ready to send",
            SendIoErrorPhase::StartSend => "starting to send",
            SendIoErrorPhase::Flush => "flushing",
            SendIoErrorPhase::Close => "closing",
        };

        write!(f, "{}", message)
    }
}

/// The concrete implementation of [WaylandState] for the wire protocol.
pub(crate) struct WireState<R, PF> {
    map: ObjectMap<PF, R>,
}

impl<R, PF> WaylandState<PF> for WireState<R, PF>
where
    Extractor: ExtractIndex<R>,
    R: Role,
{
    fn create_object(&self, f: impl Fn(ObjectId) -> PF) -> Result<Arc<PF>, WireError> {
        self.map.create(f).context(CreateObjectError {})
    }

    fn add_remote_object(&self, id: ObjectId, object: PF) {
        self.map.add(id, object);
    }

    fn remove_object(&self, id: ObjectId) {
        self.map.remove(id);
    }
}

/// The send half of the [Wayland] wire protocol.
///
/// A `WireSend` allows sending Wayland messages accross the wire-protocol wrapped channel. The
/// type of messages that can be sent depend on the role (the `R` type parameter). It can send
/// `PF::Requests` for the `ClientRole` and `PF::Events` for the `ServerRole`.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[pin_project]
pub(crate) struct WireSend<T, R, PF>
where
    PF: SendMsg<R>,
    R: Role,
{
    #[pin]
    inner: SplitSink<Transport<T, R, PF>, SendMsgType<R, PF>>,
}

impl<T, R, PF> Sink<SendMsgType<R, PF>> for WireSend<T, R, PF>
where
    PF: ProtocolFamily + SendMsg<R>,
    R: Role,
    T: IoChannel + Unpin,
{
    type Error = WireError;

    fn poll_ready(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.project().inner.poll_ready(cx).map(|r| {
            r.context(SendIoError {
                phase: SendIoErrorPhase::Ready,
            })
        })
    }

    fn start_send(self: Pin<&mut Self>, item: SendMsgType<R, PF>) -> Result<(), Self::Error> {
        self.project().inner.start_send(item).context(SendIoError {
            phase: SendIoErrorPhase::StartSend,
        })
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.project().inner.poll_flush(cx).map(|r| {
            r.context(SendIoError {
                phase: SendIoErrorPhase::Flush,
            })
        })
    }

    fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.project().inner.poll_close(cx).map(|r| {
            r.context(SendIoError {
                phase: SendIoErrorPhase::Close,
            })
        })
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
    inner: SplitStream<Transport<T, R, PF>>,
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
    Extractor: ExtractIndex<R>,
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

type Transport<T, R, PF> = WaylandTransport<T, R, PF, ObjectMap<PF, R>>;
