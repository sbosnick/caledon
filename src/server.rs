// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The server side of the higher level [Wayland] object protocol.
//!
//! [Wayland]: https://wayland.freedesktop.org/

use std::{
    error, io,
    marker::PhantomData,
    pin::Pin,
    task::{Context, Poll},
};

use futures_core::Stream;
use futures_sink::Sink;
use pin_project::pin_project;
use snafu::{IntoError, Snafu};

use crate::{
    core::{
        make_wire_protocol, ServerRole, WaylandState, WireError, WireRecv, WireSend, WireState,
    },
    protocols, IoChannel,
};

/// The core server-side object to host a [Wayland] server.
///
/// A `Server` listens on a `Stream` of `IoChannel`'s and
/// produces a `Stream` of `Display`'s for each incoming `IoChannel`.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[pin_project]
#[derive(Debug)]
pub struct Server<CS, C> {
    #[pin]
    inner: ServerImpl<CS, WireProtocol<C>>,
}

/// The server-side object that represents one connection from a client.
#[derive(Debug)]
pub struct Display<C> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    inner: DisplayImpl<WireProtocol<C>>,
}

/// The possible errors arising in the core server-side [Wayland] objects.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug, Snafu)]
pub struct ServerError(ServerErrorImpl<WireError>);

#[derive(Debug)]
struct WireProtocol<C> {
    _phantom: PhantomData<C>,
}

impl<C: IoChannel + Unpin> Wire for WireProtocol<C> {
    type Sink = WireSend<C, ServerRole, protocols::Protocols>;

    type Stream = WireRecv<C, ServerRole, protocols::Protocols>;

    type State = WireState<ServerRole, protocols::Protocols>;

    type Error = WireError;
}

impl<C: IoChannel + Unpin> WireMaker<C> for WireProtocol<C> {
    fn make(channel: C) -> (Self::Sink, Self::Stream, Self::State) {
        make_wire_protocol(channel)
    }
}

impl<CS, C> Server<CS, C>
where
    CS: Stream<Item = io::Result<C>>,
    C: IoChannel + Unpin,
{
    /// Create a new `Server`.
    pub fn new(channels: CS) -> Self {
        Self {
            inner: ServerImpl::new(channels),
        }
    }
}

impl<CS, C> Stream for Server<CS, C>
where
    CS: Stream<Item = io::Result<C>>,
    C: IoChannel + Unpin,
{
    type Item = Result<Display<C>, ServerError>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.project();
        this.inner
            .poll_next(cx)
            .map_ok(|inner| Display { inner })
            .map_err(|e| e.into())
    }
}

impl<C> Display<C> {
    /// Dispatch incoming requests.
    pub async fn dispatch(&self) {
        todo!()
    }
}

#[derive(Debug, Snafu)]
enum ServerErrorImpl<E: error::Error + 'static> {
    #[snafu(display("Error listening for incoming connections."))]
    ListenForConnection {
        source: io::Error,
    },

    Dummy {
        source: E,
    },
}

// === impl inner Server (ServerImpl) ===

#[pin_project]
#[derive(Debug)]
struct ServerImpl<CS, WM> {
    #[pin]
    channels: CS,
    _phantom: PhantomData<WM>,
}

trait Wire {
    type Sink: Sink<protocols::Events, Error = Self::Error>;
    type Stream: Stream<Item = Result<protocols::Requests, Self::Error>>;
    type State: WaylandState<protocols::Protocols, Error = Self::Error>;
    type Error: error::Error + 'static;
}

trait WireMaker<C: IoChannel>: Wire {
    fn make(channel: C) -> (Self::Sink, Self::Stream, Self::State);
}

impl<CS, C, WM> ServerImpl<CS, WM>
where
    CS: Stream<Item = io::Result<C>>,
    C: IoChannel,
    WM: WireMaker<C>,
{
    fn new(channels: CS) -> Self {
        Self {
            channels,
            _phantom: PhantomData,
        }
    }
}

impl<CS, C, WM> Stream for ServerImpl<CS, WM>
where
    CS: Stream<Item = io::Result<C>>,
    C: IoChannel,
    WM: WireMaker<C>,
{
    type Item = Result<DisplayImpl<WM>, ServerErrorImpl<WM::Error>>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.project();
        this.channels
            .poll_next(cx)
            .map_ok(|c| DisplayImpl::new(WM::make(c)))
            .map_err(|e| ListenForConnection {}.into_error(e))
    }
}

// === impl inner Diplay (DisplayImpl) ===

#[derive(Debug)]
struct DisplayImpl<W> {
    _phantom: PhantomData<W>,
}

impl<W> DisplayImpl<W>
where
    W: Wire,
{
    fn new(_: (W::Sink, W::Stream, W::State)) -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use assert_matches::assert_matches;
    use fd_queue::{DequeueFd, EnqueueFd};
    use futures::stream::{self, StreamExt};
    use tokio::io::{AsyncRead, AsyncWrite};

    struct StubChannel;

    impl AsyncRead for StubChannel {
        fn poll_read(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            _buf: &mut tokio::io::ReadBuf<'_>,
        ) -> Poll<io::Result<()>> {
            unimplemented!("method called on StubChannel")
        }
    }

    impl AsyncWrite for StubChannel {
        fn poll_write(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            _buf: &[u8],
        ) -> Poll<Result<usize, io::Error>> {
            unimplemented!("method called on StubChannel")
        }

        fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
            unimplemented!("method called on StubChannel")
        }

        fn poll_shutdown(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
        ) -> Poll<Result<(), io::Error>> {
            unimplemented!("method called on StubChannel")
        }
    }

    impl EnqueueFd for StubChannel {
        fn enqueue(
            &mut self,
            _fd: &impl std::os::unix::prelude::AsRawFd,
        ) -> Result<(), fd_queue::QueueFullError> {
            unimplemented!("method called on StubChannel")
        }
    }

    impl DequeueFd for StubChannel {
        fn dequeue(&mut self) -> Option<std::os::unix::prelude::RawFd> {
            unimplemented!("method called on StubChannel")
        }
    }

    #[derive(Debug)]
    struct FakeWireMaker;

    impl Wire for FakeWireMaker {
        type Sink = StubSink;

        type Stream = StubStream;

        type State = StubState;

        type Error = io::Error;
    }

    impl WireMaker<StubChannel> for FakeWireMaker {
        fn make(_channel: StubChannel) -> (Self::Sink, Self::Stream, Self::State) {
            (StubSink, StubStream, StubState)
        }
    }

    struct StubSink;

    impl Sink<protocols::Events> for StubSink {
        type Error = io::Error;

        fn poll_ready(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
        ) -> Poll<Result<(), Self::Error>> {
            unimplemented!("method called on StubSink")
        }

        fn start_send(self: Pin<&mut Self>, _item: protocols::Events) -> Result<(), Self::Error> {
            unimplemented!("method called on StubSink")
        }

        fn poll_flush(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
        ) -> Poll<Result<(), Self::Error>> {
            unimplemented!("method called on StubSink")
        }

        fn poll_close(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
        ) -> Poll<Result<(), Self::Error>> {
            unimplemented!("method called on StubSink")
        }
    }

    struct StubStream;

    impl Stream for StubStream {
        type Item = Result<protocols::Requests, io::Error>;

        fn poll_next(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            unimplemented!("method called on StubStream")
        }
    }

    struct StubState;

    impl WaylandState<protocols::Protocols> for StubState {
        type Error = io::Error;

        fn create_object(
            &self,
            _f: impl Fn(crate::core::ObjectId) -> protocols::Protocols,
        ) -> Result<std::sync::Arc<protocols::Protocols>, Self::Error> {
            unimplemented!("method called on StubState")
        }

        fn add_remote_object(&self, _id: crate::core::ObjectId, _object: protocols::Protocols) {
            unimplemented!("method called on StubState")
        }

        fn remove_object(&self, _id: u32) {
            unimplemented!("method called on StubState")
        }
    }

    fn make_server_impl<CS, C, WM>(channels: CS, _: WM) -> ServerImpl<CS, WM>
    where
        CS: Stream<Item = io::Result<C>>,
        C: IoChannel,
        WM: WireMaker<C>,
    {
        ServerImpl::new(channels)
    }

    #[tokio::test]
    async fn stream_impl_yields_error_on_channel_stream_error() {
        let error = io::Error::new(io::ErrorKind::Other, "some error");
        let channels = stream::iter(vec![Err(error), Ok(StubChannel)]);

        let mut sut = make_server_impl(channels, FakeWireMaker);
        let result = sut.next().await;

        assert_matches!(result, Some(Err(_)));
    }

    #[tokio::test]
    async fn stream_impl_yields_ok_on_channel_stream_ok() {
        let error = io::Error::new(io::ErrorKind::Other, "some error");
        let channels = stream::iter(vec![Ok(StubChannel), Err(error)]);

        let mut sut = make_server_impl(channels, FakeWireMaker);
        let result = sut.next().await;

        assert_matches!(result, Some(Ok(_)));
    }
}
