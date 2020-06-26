// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::ffi::CString;
use std::pin::Pin;

// TODO: remove this when no longer needed
#[allow(unused_imports)]
use fd_queue::{DequeueFd, EnqueueFd, QueueFullError};
use futures_core::{
    stream::Stream,
    task::{Context, Poll},
};
use futures_sink::Sink;
use pin_project::pin_project;
use thiserror::Error;
use tokio::io::{AsyncRead, AsyncWrite};
use tokio_util::codec::{Decoder, Framed};

use super::codec::{CodecError, WaylandCodec};
use super::{
    ClientRole, Interface, InterfaceList, Message, MessageList, Protocol, ProtocolFamily,
    ProtocolList, ServerRole,
};

// === WaylandTransport ===

#[pin_project]
pub struct WaylandTransport<T, R, P> {
    #[pin]
    inner: Framed<T, WaylandCodec<R, P>>,
}

impl<T, R, P> WaylandTransport<T, R, P>
where
    T: AsyncWrite + AsyncRead,
{
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    fn new(io: T) -> WaylandTransport<T, R, P> {
        WaylandTransport {
            inner: WaylandCodec::<R, P>::default().framed(io),
        }
    }
}

impl<T, R, P> Stream for WaylandTransport<T, R, P> {
    type Item = DispatchMessage;

    fn poll_next(self: Pin<&mut Self>, _cx: &mut Context) -> Poll<Option<Self::Item>> {
        todo!()
    }
}

impl<T,P, Item> Sink<Item> for WaylandTransport<T,ServerRole,P>
where
    Item: Message,
    <<Item as Message>::MessageList as MessageList>::Interface : Interface<
        Events = Item::MessageList,
    >,

    P: ProtocolFamily,
    <<<<<Item as Message>::MessageList as MessageList>::Interface as Interface>::InterfaceList as InterfaceList>::Protocol as Protocol>::ProtocolList : ProtocolList<
        ProtocolFamily = P,
    >,
    T: AsyncWrite+Unpin+EnqueueFd,
{
    type Error = TransportError;

    fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        Sink::<Item>::poll_ready(self.project().inner, cx).map_err(|e| e.into())
    }

    fn start_send(self: Pin<&mut Self>, msg: Item) -> Result<(), Self::Error> {
        let mut inner = self.project().inner;
        let framed: &mut Framed<T, WaylandCodec<ServerRole, P>> = &mut inner;

        msg.args().enqueue(framed.get_mut())?;
        Sink::<Item>::start_send(inner, msg).map_err(|e| e.into())
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        Sink::<Item>::poll_flush(self.project().inner, cx).map_err(|e| e.into())
    }

    fn poll_close(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        Sink::<Item>::poll_close(self.project().inner, cx).map_err(|e| e.into())
    }

}

impl<T,P, Item> Sink<Item> for WaylandTransport<T,ClientRole,P>
where
    Item: Message,
    <<Item as Message>::MessageList as MessageList>::Interface : Interface<
        Requests = Item::MessageList,
    >,

    P: ProtocolFamily,
    <<<<<Item as Message>::MessageList as MessageList>::Interface as Interface>::InterfaceList as InterfaceList>::Protocol as Protocol>::ProtocolList : ProtocolList<
        ProtocolFamily = P,
    >,
    T: AsyncWrite+Unpin+EnqueueFd,
{
    type Error = TransportError;

    fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        Sink::<Item>::poll_ready(self.project().inner, cx).map_err(|e| e.into())
    }

    fn start_send(self: Pin<&mut Self>, msg: Item) -> Result<(), Self::Error> {
        let mut inner = self.project().inner;
        let framed: &mut Framed<T, WaylandCodec<ClientRole, P>> = &mut inner;

        msg.args().enqueue(framed.get_mut())?;
        Sink::<Item>::start_send(inner, msg).map_err(|e| e.into())
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        Sink::<Item>::poll_flush(self.project().inner, cx).map_err(|e| e.into())
    }

    fn poll_close(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        Sink::<Item>::poll_close(self.project().inner, cx).map_err(|e| e.into())
    }

}

// === DispatchMessage ===

pub struct DispatchMessage {}

// === TransportError ===

#[derive(Debug, Error)]
pub enum TransportError {
    #[error("Transport unable to encode or decode a message: {source}")]
    CodecError {
        #[from]
        source: CodecError,
    },

    #[error("Transport unable to enqueue a file descriptor: {source}")]
    QueueError {
        #[from]
        source: QueueFullError,
    },
}

// === ArgEnqueueFd ===

pub trait ArgEnqueueFd {
    fn enqueue(&self, queue: &mut impl EnqueueFd) -> Result<(), TransportError>;
}

impl ArgEnqueueFd for super::Fd {
    fn enqueue(&self, queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        queue.enqueue(&self).map_err(|e| e.into())
    }
}

impl ArgEnqueueFd for i32 {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        // do nothing
        Ok(())
    }
}

impl ArgEnqueueFd for u32 {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        // do nothing
        Ok(())
    }
}

impl ArgEnqueueFd for CString {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        // do nothing
        Ok(())
    }
}

impl ArgEnqueueFd for Box<[u8]> {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        // do nothing
        Ok(())
    }
}

impl ArgEnqueueFd for super::ObjectId {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        // do nothing
        Ok(())
    }
}

impl ArgEnqueueFd for super::Decimal {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        // do nothing
        Ok(())
    }
}

impl ArgEnqueueFd for () {
    fn enqueue(&self, _queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
        Ok(())
    }
}

macro_rules! tuple_arg_enqueue_fd_impl {
    ( $($name:ident)+ ) => (
        impl<$($name: ArgEnqueueFd),*> ArgEnqueueFd for ($($name,)+) {
            #[allow(non_snake_case)]
            fn enqueue(&self, queue: &mut impl EnqueueFd) -> Result<(), TransportError> {
                let ($(ref $name,)*) = *self;
                $($name.enqueue(queue)?;)*
                Ok(())
            }
        }
    );
}

tuple_arg_enqueue_fd_impl! { A }
tuple_arg_enqueue_fd_impl! { A B }
tuple_arg_enqueue_fd_impl! { A B C }
tuple_arg_enqueue_fd_impl! { A B C D }
tuple_arg_enqueue_fd_impl! { A B C D E }
tuple_arg_enqueue_fd_impl! { A B C D E F }
tuple_arg_enqueue_fd_impl! { A B C D E F G }
tuple_arg_enqueue_fd_impl! { A B C D E F G H }
tuple_arg_enqueue_fd_impl! { A B C D E F G H I }
tuple_arg_enqueue_fd_impl! { A B C D E F G H I J }
tuple_arg_enqueue_fd_impl! { A B C D E F G H I J K }
tuple_arg_enqueue_fd_impl! { A B C D E F G H I J K L }

#[cfg(test)]
mod tests {
    use super::*;

    use std::io;
    use std::os::unix::io::{AsRawFd, RawFd};

    use futures::executor::block_on;
    use futures::sink::SinkExt;
    use futures_ringbuf::RingBuffer as AsyncRingBuffer;
    use ringbuf::{Consumer, Producer, RingBuffer};

    use crate::core::testutil::{Family, FdEvent};
    use crate::core::{Decimal, Fd, ObjectId};

    struct MockQueue(Option<RawFd>);

    impl EnqueueFd for MockQueue {
        fn enqueue(&mut self, fd: &impl AsRawFd) -> Result<(), QueueFullError> {
            match self.0 {
                Some(expected) => assert_eq!(fd.as_raw_fd(), expected, "Unexpected fd."),
                None => panic!("enqueue() called unexpectedly"),
            }
            Ok(())
        }
    }

    #[test]
    fn arg_enqueue_for_fd_enqueues_fd() {
        let expected_fd = 1;
        let mut queue = MockQueue(Some(expected_fd));

        let sut = Fd(expected_fd);
        sut.enqueue(&mut queue).unwrap();
    }

    #[test]
    fn arg_enqueue_for_others_does_not_enqueue() {
        arg_enqueue_does_not_enqueue(1i32);
        arg_enqueue_does_not_enqueue(1u32);
        arg_enqueue_does_not_enqueue(CString::new("hello").unwrap());
        arg_enqueue_does_not_enqueue(vec![b'h', b'e'].into_boxed_slice());
        arg_enqueue_does_not_enqueue(Decimal(1));
        arg_enqueue_does_not_enqueue(ObjectId(1));
    }

    fn arg_enqueue_does_not_enqueue<T: ArgEnqueueFd>(sut: T) {
        let mut queue = MockQueue(None);

        sut.enqueue(&mut queue).unwrap();
    }

    #[test]
    fn arg_enqueue_for_tuple_enqueues_fd() {
        let expected_fd = 1;
        let mut queue = MockQueue(Some(expected_fd));

        let sut = (Fd(expected_fd), 3u32);
        sut.enqueue(&mut queue).unwrap();
    }

    #[test]
    fn arg_enqueue_for_no_fd_tuple_does_not_enqueue() {
        arg_enqueue_does_not_enqueue((3u32, 4i32));
    }

    #[pin_project]
    struct FakeEndpoint {
        producer: Producer<RawFd>,
        consumer: Consumer<RawFd>,
        #[pin]
        io: AsyncRingBuffer<u8>,
    }

    impl Default for FakeEndpoint {
        fn default() -> Self {
            let (producer, consumer) = RingBuffer::new(2).split();
            FakeEndpoint {
                producer,
                consumer,
                io: AsyncRingBuffer::new(1024),
            }
        }
    }

    impl AsyncRead for FakeEndpoint {
        fn poll_read(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &mut [u8],
        ) -> Poll<io::Result<usize>> {
            self.project().io.poll_read(cx, buf)
        }
    }

    impl AsyncWrite for FakeEndpoint {
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<Result<usize, io::Error>> {
            self.project().io.poll_write(cx, buf)
        }

        fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
            self.project().io.poll_flush(cx)
        }

        fn poll_shutdown(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
        ) -> Poll<Result<(), io::Error>> {
            self.project().io.poll_shutdown(cx)
        }
    }

    impl EnqueueFd for FakeEndpoint {
        fn enqueue(&mut self, fd: &impl AsRawFd) -> Result<(), QueueFullError> {
            self.producer
                .push(fd.as_raw_fd())
                .map_err(|_| QueueFullError::new())
        }
    }

    impl DequeueFd for FakeEndpoint {
        fn dequeue(&mut self) -> Option<RawFd> {
            self.consumer.pop()
        }
    }

    #[test]
    fn transport_passes_fd() {
        let endpoint = FakeEndpoint::default();
        let message = FdEvent::new(ObjectId(2), Fd(4));

        let mut sut = WaylandTransport::<_, ServerRole, Family>::new(endpoint);
        block_on(sut.send(message)).expect("Unable to send message.");

        assert!(!sut.inner.get_ref().consumer.is_empty());
    }
}
