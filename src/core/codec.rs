// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::ffi::CString;
use std::io;
use std::marker::PhantomData;
use std::mem;

use bytes::{BufMut, Bytes, BytesMut};
use thiserror::Error;
use tokio_util::codec::{Decoder, Encoder};

use super::{
    Client, Interface, InterfaceList, Message, MessageList, ObjectId, Protocol, ProtocolFamily,
    ProtocolList, Role, Server,
};

// === Codec ===

pub(crate) struct Codec<R, P> {
    _marker: PhantomData<(R, P)>,
}

impl<R, P> Codec<R, P> {
    // TODO remove this when it is no longer needed
    #[allow(dead_code)]
    pub(crate) fn new(_role: R, _family: P) -> Codec<R, P> {
        Codec {
            _marker: PhantomData,
        }
    }
}

impl<R, P> Codec<R, P>
where
    R: Role,
    P: ProtocolFamily,
{
    fn write_message<T>(&mut self, item: T, dst: &mut BytesMut) -> Result<(), CodecError>
    where
        T: Message,
    {
        let len = mem::size_of::<WaylandHeader>() + item.args().len() as usize;
        if len > u16::MAX as usize {
            return Err(CodecError::MessageTooLong {
                object: item.sender(),
            });
        }

        dst.reserve(len);

        WaylandHeader::new(item.sender().0, len as u16, T::OPCODE).write(dst);
        item.args().write(dst);

        Ok(())
    }
}

impl<T, P> Encoder<T> for Codec<Server, P>
where
    T: Message,
    <<T as Message>::MessageList as MessageList>::Interface : Interface<
        Events = T::MessageList,
    >,

    P: ProtocolFamily,
    <<<<<T as Message>::MessageList as MessageList>::Interface as Interface>::InterfaceList as InterfaceList>::Protocol as Protocol>::ProtocolList : ProtocolList<
        ProtocolFamily = P,
    >,
{
    type Error = CodecError;

    fn encode(&mut self, item: T, dst: &mut BytesMut) -> Result<(), Self::Error> {
        self.write_message(item, dst)
    }
}

impl<T, P> Encoder<T> for Codec<Client, P>
where
    T: Message,
    <<T as Message>::MessageList as MessageList>::Interface : Interface<
        Requests = T::MessageList,
    >,

    P: ProtocolFamily,
    <<<<<T as Message>::MessageList as MessageList>::Interface as Interface>::InterfaceList as InterfaceList>::Protocol as Protocol>::ProtocolList : ProtocolList<
        ProtocolFamily = P,
    >,
{
    type Error = CodecError;

    fn encode(&mut self, item: T, dst: &mut BytesMut) -> Result<(), Self::Error> {
        self.write_message(item, dst)
    }
}

impl<R, P> Decoder for Codec<R, P> {
    type Item = DispatchMessage;
    type Error = CodecError;

    fn decode(&mut self, _src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        todo!()
    }
}

// === WaylandHeader ===

#[repr(C)]
struct WaylandHeader {
    sender: u32,

    // This isn't 2 u16's to make sure we maintain host endianness for this as a u32.
    len_opcode: u32,
}

impl WaylandHeader {
    fn new(sender: u32, len: u16, obcode: u16) -> WaylandHeader {
        WaylandHeader {
            sender,
            len_opcode: ((len as u32) << 16) | (obcode as u32),
        }
    }

    // TODO: remove this when no longer needed
    #[allow(dead_code)]
    fn sender(&self) -> u32 {
        self.sender
    }

    // TODO: remove this when no longer needed
    #[allow(dead_code)]
    fn len(&self) -> u16 {
        (self.len_opcode >> 16) as u16
    }

    // TODO: remove this when no longer needed
    #[allow(dead_code)]
    fn opcode(&self) -> u16 {
        (self.len_opcode & 0xFF) as u16
    }

    fn write(&self, dst: &mut impl BufMut) {
        write_u32(self.sender, dst);
        write_u32(self.len_opcode, dst);
    }
}

// === DispatchMessage ===

pub struct DispatchMessage {
    _object_id: ObjectId,
    _opcode: u16,
    _args: Bytes,
}

// === CodecError ===

#[derive(Debug, Error)]
pub enum CodecError {
    #[error("io error: {source}")]
    Io {
        #[from]
        source: io::Error,
    },

    #[error("message sent from object {} is too long", object.0)]
    MessageTooLong { object: ObjectId },
}

// === ArgWriter ===

/// ArgWriter is the low-level interface to write the 7 argument types into the byte
/// stream as a part of the Wayland wire protocol. ArgWriter does not handle fd
/// passing which will be dealt with at a higher level.
pub trait ArgWriter {
    fn len(&self) -> u16;
    fn write(&self, dst: &mut impl BufMut);
}

impl ArgWriter for i32 {
    fn len(&self) -> u16 {
        mem::size_of::<Self>() as u16
    }

    fn write(&self, dst: &mut impl BufMut) {
        write_i32(*self, dst)
    }
}

impl ArgWriter for u32 {
    fn len(&self) -> u16 {
        mem::size_of::<Self>() as u16
    }

    fn write(&self, dst: &mut impl BufMut) {
        write_u32(*self, dst)
    }
}

impl ArgWriter for super::Decimal {
    fn len(&self) -> u16 {
        mem::size_of_val(&self.0) as u16
    }

    fn write(&self, dst: &mut impl BufMut) {
        write_u32(self.0, dst)
    }
}

impl ArgWriter for CString {
    fn len(&self) -> u16 {
        let length_size = mem::size_of::<u32>() as u16;
        let content_size = self.as_bytes_with_nul().len() as u16;
        align_up::<u32>(length_size + content_size)
    }

    fn write(&self, dst: &mut impl BufMut) {
        let contents = self.as_bytes_with_nul();
        let padding = padding::<u32>(contents.len() as u16);

        write_u32(contents.len() as u32, dst);
        dst.put_slice(contents);
        for _ in 0..padding {
            dst.put_u8(0);
        }
    }
}

impl ArgWriter for super::ObjectId {
    fn len(&self) -> u16 {
        mem::size_of_val(&self.0) as u16
    }

    fn write(&self, dst: &mut impl BufMut) {
        write_u32(self.0, dst)
    }
}

impl ArgWriter for Box<[u8]> {
    fn len(&self) -> u16 {
        let length_size = mem::size_of::<u32>() as u16;
        let content_size = self.as_ref().len() as u16;
        align_up::<u32>(length_size + content_size)
    }

    fn write(&self, dst: &mut impl BufMut) {
        let contents = self.as_ref();
        let padding = padding::<u32>(contents.len() as u16);

        write_u32(contents.len() as u32, dst);
        dst.put_slice(contents);
        for _ in 0..padding {
            dst.put_u8(0);
        }
    }
}

impl ArgWriter for super::Fd {
    fn len(&self) -> u16 {
        0
    }

    fn write(&self, _dst: &mut impl BufMut) {
        // nothing to write as Fd's are passed differently
    }
}

impl ArgWriter for () {
    fn len(&self) -> u16 {
        0
    }

    fn write(&self, _dst: &mut impl BufMut) {
        // an empty tuple has nothing to write
    }
}

macro_rules! tuple_arg_writer_impl {
    ( $($name:ident)+ ) => (
        #[allow(non_snake_case)]
        impl<$($name: ArgWriter),*> ArgWriter for ($($name,)+) {
            fn len(&self) -> u16 {
                let ($(ref $name,)*) = *self;
                $($name.len() +)* 0
            }

            fn write(&self, dst: &mut impl BufMut) {
                let ($(ref $name,)*) = *self;
                $($name.write(dst);)*
            }
        }
    );
}

tuple_arg_writer_impl! { A }
tuple_arg_writer_impl! { A B }
tuple_arg_writer_impl! { A B C }
tuple_arg_writer_impl! { A B C D }
tuple_arg_writer_impl! { A B C D E }
tuple_arg_writer_impl! { A B C D E F }
tuple_arg_writer_impl! { A B C D E F G }
tuple_arg_writer_impl! { A B C D E F G H }
tuple_arg_writer_impl! { A B C D E F G H I }
tuple_arg_writer_impl! { A B C D E F G H I J }
tuple_arg_writer_impl! { A B C D E F G H I J K }
tuple_arg_writer_impl! { A B C D E F G H I J K L }

fn padding<T>(val: u16) -> u16 {
    let align = mem::size_of::<T>() as u16;

    (align - val % align) % align
}

fn align_up<T>(val: u16) -> u16 {
    val + padding::<T>(val)
}

#[cfg(target_endian = "little")]
fn write_u32(val: u32, dst: &mut impl BufMut) {
    dst.put_u32_le(val)
}

#[cfg(target_endian = "big")]
fn write_u32(val: u32, dst: &mut impl BufMut) {
    dst.put_u32(val)
}

#[cfg(target_endian = "little")]
fn write_i32(val: i32, dst: &mut impl BufMut) {
    dst.put_i32_le(val)
}

#[cfg(target_endian = "big")]
fn write_i32(val: i32, dst: &mut impl BufMut) {
    dst.put_i32(val)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::core::testutil::{DestroyRequest, Family, PreFdEvent};
    use crate::core::{Decimal, Fd, ObjectId};

    #[test]
    fn encode_messages_by_role() {
        let mut server = Codec::new(Server {}, Family {});
        let mut client = Codec::new(Client {}, Family {});
        let mut buffer = BytesMut::new();

        client.encode(DestroyRequest {}, &mut buffer).unwrap();
        server.encode(PreFdEvent {}, &mut buffer).unwrap();

        // The next 2 lines are compiler errors because of a mismatch between
        // Client/Server and Event/Requests.  server.encode(DestroyRequest{}, &mut
        // buffer).unwrap(); client.encode(PreFdEvent{}, &mut buffer).unwrap();
    }

    #[test]
    fn encode_message_gives_expected_bytes() {
        let mut buffer = BytesMut::new();

        let mut sut = Codec::new(Client {}, Family {});
        sut.encode(DestroyRequest {}, &mut buffer).unwrap();

        assert_eq!(
            buffer,
            &[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00,].as_ref()
        );
    }

    #[test]
    fn arg_writer_for_fixed_size_gives_expected_len() {
        assert_eq!(1i32.len(), 4);
        assert_eq!(1u32.len(), 4);
        assert_eq!(Decimal(1).len(), 4);
        assert_eq!(ObjectId(1).len(), 4);
        assert_eq!(Fd(0).len(), 0);
    }

    #[test]
    fn arg_writer_for_cstring_gives_expected_len() {
        let sut = CString::new("hello").expect("bad CString");
        let result = sut.len();

        assert_eq!(result, 12);
    }

    #[test]
    fn arg_writer_for_box_u8_slice_gives_expected_len() {
        let vec = vec![b'h', b'e', b'l', b'l', b'o'];

        let sut = vec.into_boxed_slice();
        let result = sut.len();

        assert_eq!(result, 12);
    }

    #[test]
    fn arg_writer_writes_u32() {
        arg_writer_writes_value(1u32, &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_writer_writes_i32() {
        arg_writer_writes_value(1i32, &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_writer_writes_decimal() {
        arg_writer_writes_value(Decimal(1), &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_writer_writes_object_id() {
        arg_writer_writes_value(ObjectId(1), &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_writer_writes_nothing_for_fd() {
        let mut buf = BytesMut::with_capacity(50);

        let sut = Fd(1);
        sut.write(&mut buf);

        assert!(buf.is_empty());
    }

    #[test]
    fn arg_writer_writes_cstring() {
        let expected = &[
            0x06, 0x00, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o', 0x00, 0x00, 0x00,
        ];

        let sut = CString::new("hello").expect("bad CString");

        arg_writer_writes_value(sut, expected);
    }

    #[test]
    fn arg_writer_writes_box_u8_slice() {
        let expected = &[
            0x05, 0x00, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o', 0x00, 0x00, 0x00,
        ];
        let vec = vec![b'h', b'e', b'l', b'l', b'o'];

        let sut = vec.into_boxed_slice();

        arg_writer_writes_value(sut, expected);
    }

    #[test]
    fn tuple_u8_cstring_writes_expected_value() {
        let expected = &[
            0x01, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o', 0x00,
            0x00, 0x00,
        ];
        let hello = CString::new("hello").expect("bad CString");

        let sut = (1u32, hello);

        arg_writer_writes_value(sut, expected);
    }

    fn arg_writer_writes_value(sut: impl ArgWriter, expected: &[u8]) {
        let mut buf = BytesMut::with_capacity(50);

        sut.write(&mut buf);

        assert_eq!(buf, expected);
    }
}
