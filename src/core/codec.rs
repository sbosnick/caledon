// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::fmt::Debug;
use std::ffi::{self, CString};
use std::io;
use std::marker::PhantomData;
use std::mem;

use bytes::{Buf, BufMut, Bytes, BytesMut};
use thiserror::Error;
use tokio_util::codec::{Decoder, Encoder};

use super::{
    Client, Interface, InterfaceList, Message, MessageList, ObjectId, Protocol, ProtocolFamily,
    ProtocolList, Role, Server, Signature,
};

// === WaylandCodec ===

pub(crate) struct WaylandCodec<R, P> {
    decode_state: DecodeState,
    _marker: PhantomData<(R, P)>,
}

impl<R, P> WaylandCodec<R, P> {
    // TODO remove this when it is no longer needed
    #[allow(dead_code)]
    pub(crate) fn new(_role: R, _family: P) -> WaylandCodec<R, P> {
        WaylandCodec {
            decode_state: DecodeState::Head,
            _marker: PhantomData,
        }
    }
}

impl<R, P> WaylandCodec<R, P>
where
    R: Role,
    P: ProtocolFamily,
{
    fn encode_message<T>(&mut self, item: T, dst: &mut BytesMut) -> Result<(), CodecError>
    where
        T: Message,
    {
        let len = WaylandHeader::size() + item.args().len() as usize;
        if len > u16::MAX as usize {
            return Err(CodecError::MessageTooLong {
                object: item.sender(),
            });
        }

        dst.reserve(len);

        WaylandHeader::new(item.sender().0, len as u16, T::OPCODE).encode(dst);
        item.args().encode(dst);

        Ok(())
    }
}

impl<T, P> Encoder<T> for WaylandCodec<Server, P>
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
        self.encode_message(item, dst)
    }
}

impl<T, P> Encoder<T> for WaylandCodec<Client, P>
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
        self.encode_message(item, dst)
    }
}

impl<R, P> Decoder for WaylandCodec<R, P> {
    type Item = DispatchMessage;
    type Error = CodecError;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        let head = match &self.decode_state {
            DecodeState::Head => match WaylandHeader::decode(src) {
                None => {
                    src.reserve(WaylandHeader::size() - src.len());
                    return Ok(None);
                }
                Some(head) => {
                    self.decode_state = DecodeState::Args(head);
                    head
                }
            },
            DecodeState::Args(head) => *head,
        };

        if src.len() < head.len() as usize - WaylandHeader::size() {
            // Reserve space for the remaining bytes of this messages and the header
            // of the next message. Since head.len() includes the current header
            // bytes we don't have to add WaylandHeader::size() again.
            src.reserve(head.len() as usize - src.len());
            Ok(None)
        } else {
            let args = src
                .split_to(head.len() as usize - WaylandHeader::size())
                .freeze();
            src.reserve(WaylandHeader::size() - src.len());
            self.decode_state = DecodeState::Head;

            Ok(Some(DispatchMessage {
                object_id: ObjectId(head.sender()),
                opcode: head.opcode(),
                args,
            }))
        }
    }
}

// === WaylandHeader ===

#[derive(Clone, Copy)]
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

    fn size() -> usize {
        2 * mem::size_of::<u32>()
    }

    fn sender(&self) -> u32 {
        self.sender
    }

    fn len(&self) -> u16 {
        (self.len_opcode >> 16) as u16
    }

    fn opcode(&self) -> u16 {
        (self.len_opcode & 0xFF) as u16
    }

    fn encode(&self, dst: &mut impl BufMut) {
        encode_u32(self.sender, dst);
        encode_u32(self.len_opcode, dst);
    }

    fn decode(src: &mut impl Buf) -> Option<WaylandHeader> {
        if src.remaining() < WaylandHeader::size() {
            None
        } else {
            Some(WaylandHeader {
                sender: decode_u32(src),
                len_opcode: decode_u32(src),
            })
        }
    }
}

// === DecodeState ===

enum DecodeState {
    Head,
    Args(WaylandHeader),
}

// === DispatchMessage ===

#[derive(Debug, PartialEq)]
pub struct DispatchMessage {
    object_id: ObjectId,
    opcode: u16,
    args: Bytes,
}

// TODO: remove this when it is no longer needed
#[allow(dead_code)]
impl DispatchMessage {
    pub fn object_id(&self) -> ObjectId {
        self.object_id
    }

    pub fn opcode(&self) -> u16 {
        self.opcode
    }

    pub fn extract_args<S: Signature>(&mut self) -> Result<S, CodecError> {
        S::decode(&mut self.args)
    }
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

    #[error("string argument contained unexpected nul bytes")]
    InvalidStringArg {
        #[from]
        source: ffi::NulError,
    }
}

// === ArgEncoder ===

/// ArgEncoder is the low-level interface to encode the 7 argument types into the byte
/// stream as a part of the Wayland wire protocol. ArgEncoder does not handle fd
/// passing which will be dealt with at a higher level.
pub trait ArgEncoder {
    fn len(&self) -> u16;
    fn encode(&self, dst: &mut impl BufMut);
}

impl ArgEncoder for i32 {
    fn len(&self) -> u16 {
        mem::size_of::<Self>() as u16
    }

    fn encode(&self, dst: &mut impl BufMut) {
        encode_i32(*self, dst)
    }
}

impl ArgEncoder for u32 {
    fn len(&self) -> u16 {
        mem::size_of::<Self>() as u16
    }

    fn encode(&self, dst: &mut impl BufMut) {
        encode_u32(*self, dst)
    }
}

impl ArgEncoder for super::Decimal {
    fn len(&self) -> u16 {
        mem::size_of_val(&self.0) as u16
    }

    fn encode(&self, dst: &mut impl BufMut) {
        encode_u32(self.0, dst)
    }
}

impl ArgEncoder for CString {
    fn len(&self) -> u16 {
        let length_size = mem::size_of::<u32>() as u16;
        let content_size = self.as_bytes_with_nul().len() as u16;
        align_up::<u32>(length_size + content_size)
    }

    fn encode(&self, dst: &mut impl BufMut) {
        let contents = self.as_bytes_with_nul();
        let padding = padding::<u32>(contents.len() as u16);

        encode_u32(contents.len() as u32, dst);
        dst.put_slice(contents);
        for _ in 0..padding {
            dst.put_u8(0);
        }
    }
}

impl ArgEncoder for super::ObjectId {
    fn len(&self) -> u16 {
        mem::size_of_val(&self.0) as u16
    }

    fn encode(&self, dst: &mut impl BufMut) {
        encode_u32(self.0, dst)
    }
}

impl ArgEncoder for Box<[u8]> {
    fn len(&self) -> u16 {
        let length_size = mem::size_of::<u32>() as u16;
        let content_size = self.as_ref().len() as u16;
        align_up::<u32>(length_size + content_size)
    }

    fn encode(&self, dst: &mut impl BufMut) {
        let contents = self.as_ref();
        let padding = padding::<u32>(contents.len() as u16);

        encode_u32(contents.len() as u32, dst);
        dst.put_slice(contents);
        for _ in 0..padding {
            dst.put_u8(0);
        }
    }
}

impl ArgEncoder for super::Fd {
    fn len(&self) -> u16 {
        0
    }

    fn encode(&self, _dst: &mut impl BufMut) {
        // nothing to encode as Fd's are passed differently
    }
}

impl ArgEncoder for () {
    fn len(&self) -> u16 {
        0
    }

    fn encode(&self, _dst: &mut impl BufMut) {
        // an empty tuple has nothing to encode
    }
}

macro_rules! tuple_arg_encoder_impl {
    ( $($name:ident)+ ) => (
        #[allow(non_snake_case)]
        impl<$($name: ArgEncoder),*> ArgEncoder for ($($name,)+) {
            fn len(&self) -> u16 {
                let ($(ref $name,)*) = *self;
                $($name.len() +)* 0
            }

            fn encode(&self, dst: &mut impl BufMut) {
                let ($(ref $name,)*) = *self;
                $($name.encode(dst);)*
            }
        }
    );
}

tuple_arg_encoder_impl! { A }
tuple_arg_encoder_impl! { A B }
tuple_arg_encoder_impl! { A B C }
tuple_arg_encoder_impl! { A B C D }
tuple_arg_encoder_impl! { A B C D E }
tuple_arg_encoder_impl! { A B C D E F }
tuple_arg_encoder_impl! { A B C D E F G }
tuple_arg_encoder_impl! { A B C D E F G H }
tuple_arg_encoder_impl! { A B C D E F G H I }
tuple_arg_encoder_impl! { A B C D E F G H I J }
tuple_arg_encoder_impl! { A B C D E F G H I J K }
tuple_arg_encoder_impl! { A B C D E F G H I J K L }

// === ArgDecoder ===

/// ArgDecoder is the low-level interface to decode the 7 argument types from the
/// byte stream as a part of the Wayland wire protocol. ArgDecoder does not handle fd
/// passing which will be dealt with at a higher level (the return value from
/// Fd::decode() is a fake value that should be replaced at the higher level).
pub trait ArgDecoder: Sized {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError>;
}

impl ArgDecoder for i32 {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
        Ok(decode_i32(src))
    }
}

impl ArgDecoder for u32 {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
        Ok(decode_u32(src))
    }
}

impl ArgDecoder for super::Decimal {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
        Ok(Self(decode_u32(src)))
    }
}

impl ArgDecoder for CString {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
        let len = decode_u32(src);
        let padding = padding::<u32>(len as u16);

        let mut buf = vec![0; len as usize - 1];
        src.copy_to_slice(&mut buf);

        // advance past the nul byte and the padding
        src.advance(1 + padding as usize);

        Ok(CString::new(buf)?)
    }
}

impl ArgDecoder for super::ObjectId {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
        Ok(Self(decode_u32(src)))
    }
}

impl ArgDecoder for Box<[u8]> {
    fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
        let len = decode_u32(src);
        let mut buf = vec![0; len as usize];
        src.copy_to_slice(&mut buf);

        Ok(buf.into_boxed_slice())
    }
}

impl ArgDecoder for super::Fd {
    fn decode(_src: &mut impl Buf) -> Result<Self, CodecError> {
        // Fd's take up 0 space in the byte stream as they are passed differently.
        // Return a dummy Fd on the assumption that a higher later will replace it
        // with the actual Fd.
        Ok(Self(0))
    }
}

impl ArgDecoder for () {
    fn decode(_src: &mut impl Buf) -> Result<Self, CodecError> {
        Ok(())
    }
}

macro_rules! tuple_arg_decoder_impl {
    ( $($name:ident)+ ) => (
        #[allow(non_snake_case)]
        impl<$($name: ArgDecoder),*> ArgDecoder for ($($name,)+) {
            fn decode(src: &mut impl Buf) -> Result<Self, CodecError> {
                $(let $name = $name::decode(src)?;)*

                Ok( ( $($name,)* ))
            }
        }
    );
}

tuple_arg_decoder_impl! { A }
tuple_arg_decoder_impl! { A B }
tuple_arg_decoder_impl! { A B C }
tuple_arg_decoder_impl! { A B C D }
tuple_arg_decoder_impl! { A B C D E }
tuple_arg_decoder_impl! { A B C D E F }
tuple_arg_decoder_impl! { A B C D E F G }
tuple_arg_decoder_impl! { A B C D E F G H }
tuple_arg_decoder_impl! { A B C D E F G H I }
tuple_arg_decoder_impl! { A B C D E F G H I J }
tuple_arg_decoder_impl! { A B C D E F G H I J K }
tuple_arg_decoder_impl! { A B C D E F G H I J K L }

// === utility functions ===

fn padding<T>(val: u16) -> u16 {
    let align = mem::size_of::<T>() as u16;

    (align - val % align) % align
}

fn align_up<T>(val: u16) -> u16 {
    val + padding::<T>(val)
}

#[cfg(target_endian = "little")]
fn encode_u32(val: u32, dst: &mut impl BufMut) {
    dst.put_u32_le(val)
}

#[cfg(target_endian = "big")]
fn encode_u32(val: u32, dst: &mut impl BufMut) {
    dst.put_u32(val)
}

#[cfg(target_endian = "little")]
fn encode_i32(val: i32, dst: &mut impl BufMut) {
    dst.put_i32_le(val)
}

#[cfg(target_endian = "big")]
fn encode_i32(val: i32, dst: &mut impl BufMut) {
    dst.put_i32(val)
}

#[cfg(target_endian = "little")]
fn decode_u32(src: &mut impl Buf) -> u32 {
    src.get_u32_le()
}

#[cfg(target_endian = "big")]
fn decode_u32(src: &mut impl Buf) -> u32 {
    src.get_u32()
}

#[cfg(target_endian = "little")]
fn decode_i32(src: &mut impl Buf) -> i32 {
    src.get_i32_le()
}

#[cfg(target_endian = "big")]
fn decode_i32(src: &mut impl Buf) -> i32 {
    src.get_i32()
}

#[cfg(test)]
mod tests {
    use super::*;

    use assert_matches::assert_matches;

    use crate::core::testutil::{DestroyRequest, Family, PreFdEvent};
    use crate::core::{Decimal, Fd, ObjectId};

    #[test]
    fn encode_messages_by_role() {
        let mut server = WaylandCodec::new(Server {}, Family {});
        let mut client = WaylandCodec::new(Client {}, Family {});
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

        let mut sut = WaylandCodec::new(Client {}, Family {});
        sut.encode(DestroyRequest {}, &mut buffer).unwrap();

        assert_eq!(
            buffer,
            &[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00,].as_ref()
        );
    }

    #[test]
    fn arg_encoder_for_fixed_size_gives_expected_len() {
        assert_eq!(1i32.len(), 4);
        assert_eq!(1u32.len(), 4);
        assert_eq!(Decimal(1).len(), 4);
        assert_eq!(ObjectId(1).len(), 4);
        assert_eq!(Fd(0).len(), 0);
    }

    #[test]
    fn arg_encoder_for_cstring_gives_expected_len() {
        let sut = CString::new("hello").expect("bad CString");
        let result = sut.len();

        assert_eq!(result, 12);
    }

    #[test]
    fn arg_encoder_for_box_u8_slice_gives_expected_len() {
        let vec = vec![b'h', b'e', b'l', b'l', b'o'];

        let sut = vec.into_boxed_slice();
        let result = sut.len();

        assert_eq!(result, 12);
    }

    #[test]
    fn arg_encoder_encodes_u32() {
        arg_encoder_encodes_value(1u32, &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_encoder_encodes_i32() {
        arg_encoder_encodes_value(1i32, &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_encoder_encodes_decimal() {
        arg_encoder_encodes_value(Decimal(1), &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_encoder_encodes_object_id() {
        arg_encoder_encodes_value(ObjectId(1), &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn arg_encoder_encodes_nothing_for_fd() {
        let mut buf = BytesMut::with_capacity(50);

        let sut = Fd(1);
        sut.encode(&mut buf);

        assert!(buf.is_empty());
    }

    #[test]
    fn arg_encoder_encodes_cstring() {
        let expected = &[
            0x06, 0x00, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o', 0x00, 0x00, 0x00,
        ];

        let sut = CString::new("hello").expect("bad CString");

        arg_encoder_encodes_value(sut, expected);
    }

    #[test]
    fn arg_encoder_encodes_box_u8_slice() {
        let expected = &[
            0x05, 0x00, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o', 0x00, 0x00, 0x00,
        ];
        let vec = vec![b'h', b'e', b'l', b'l', b'o'];

        let sut = vec.into_boxed_slice();

        arg_encoder_encodes_value(sut, expected);
    }

    #[test]
    fn tuple_u8_cstring_encodes_expected_value() {
        let expected = &[
            0x01, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o', 0x00,
            0x00, 0x00,
        ];
        let hello = CString::new("hello").expect("bad CString");

        let sut = (1u32, hello);

        arg_encoder_encodes_value(sut, expected);
    }

    fn arg_encoder_encodes_value(sut: impl ArgEncoder, expected: &[u8]) {
        let mut buf = BytesMut::with_capacity(50);

        sut.encode(&mut buf);

        assert_eq!(buf, expected);
    }

    #[test]
    fn arg_decoder_decodes_u32() {
        arg_decoder_decodes_value(&[1, 0, 0, 0], 1u32);
    }

    #[test]
    fn arg_decoder_decodes_i32() {
        arg_decoder_decodes_value(&[1, 0, 0, 0], 1i32);
    }

    #[test]
    fn arg_decoder_decodes_decemial() {
        arg_decoder_decodes_value(&[1, 0, 0, 0], Decimal(1));
    }

    #[test]
    fn arg_decoder_decodes_object_id() {
        arg_decoder_decodes_value(&[1, 0, 0, 0], ObjectId(1));
    }

    #[test]
    fn arg_decoder_uses_no_bytes_for_fd() {
        let array = &[1u8, 0, 0, 0];
        let mut buf = array.as_ref();

        Fd::decode(&mut buf).expect("Unexpected error in decode()");

        assert_eq!(buf.len(), 4);
    }

    #[test]
    fn arg_decoder_decodes_cstring() {
        let array = &[6, 0, 0, 0, b'h', b'e', b'l', b'l', b'o', 0, 0, 0];
        let mut buf = array.as_ref();

        let result = CString::decode(&mut buf);

        assert_matches!(result, Ok(string) => {
            assert_eq!(string, CString::new("hello").unwrap());
        });
    }

    #[test]
    fn arg_decoder_invalid_cstring_is_error() {
        // array has a nul byte in the middle of the CString portion
        let array = &[6, 0, 0, 0, b'h', b'e', b'l', 0, b'o', 0, 0, 0];
        let mut buf = array.as_ref();

        let result = CString::decode(&mut buf);

        assert_matches!(result, Err(CodecError::InvalidStringArg{source: _}));
    }

    #[test]
    fn arg_decoder_decodes_array() {
        let array = &[5, 0, 0, 0, b'h', b'e', b'l', b'l', b'o', 0, 0, 0];
        let mut buf = array.as_ref();
        let expected = vec![b'h', b'e', b'l', b'l', b'o'];

        let result = Box::<[u8]>::decode(&mut buf);

        assert_matches!(result, Ok(array) => {
            assert_eq!(array, expected.into_boxed_slice());
        });
    }

    #[test]
    fn tuple_u8_cstring_decodes_from_bytes() {
        let buf = &[1, 0, 0, 0, 6, 0, 0, 0, b'h', b'e', b'l', b'l', b'o', 0, 0, 0];
        let string = CString::new("hello").expect("bad CString");

        arg_decoder_decodes_value(buf, (1u32, string));
    }

    fn arg_decoder_decodes_value<A>(mut src: &[u8], expected: A)
    where
        A: ArgDecoder+Debug+PartialEq
    {
        let result = A::decode(&mut src).expect("Decode failed unexpectedly.");

        assert_eq!(result, expected);
    }

    #[test]
    fn decode_header_without_enough_wants_more() {
        let mut buf: BytesMut = [0x01u8, 0x00, 0x00, 0x00].as_ref().into();

        let mut sut = WaylandCodec::new(Server {}, Family {});
        let result = sut.decode(&mut buf);

        assert_matches!(result, Ok(None));
    }

    #[test]
    fn decode_empty_header_wants_more() {
        let mut buf = BytesMut::new();

        let mut sut = WaylandCodec::new(Server {}, Family {});
        let result = sut.decode(&mut buf);

        assert_matches!(result, Ok(None));
    }

    #[test]
    fn decode_header_without_args_gives_expected_result() {
        let mut buf: BytesMut = [1u8, 0, 0, 0, 0, 0, 8, 0].as_ref().into();

        let mut sut = WaylandCodec::new(Server {}, Family {});
        let result = sut.decode(&mut buf);

        assert_matches!(result, Ok(Some(msg)) => {
            assert_eq!(msg.object_id, ObjectId(1));
            assert_eq!(msg.opcode(), 0);
            assert_eq!(msg.args.len(), 0);
        });
    }

    #[test]
    fn decode_header_without_expected_args_wants_more() {
        let mut buf: BytesMut = [1u8, 0, 0, 0, 0, 0, 12, 0].as_ref().into();

        let mut sut = WaylandCodec::new(Server {}, Family {});
        let result = sut.decode(&mut buf);

        assert_matches!(result, Ok(None));
    }

    #[test]
    fn decode_header_with_args_gives_expected_result() {
        let mut buf: BytesMut = [1u8, 0, 0, 0, 0, 0, 12, 0, 2, 0, 0, 0].as_ref().into();

        let mut sut = WaylandCodec::new(Server {}, Family {});
        let result = sut.decode(&mut buf);

        assert_matches!(result, Ok(Some(msg)) => {
            assert_eq!(msg.object_id, ObjectId(1));
            assert_eq!(msg.opcode(), 0);
            assert_eq!(msg.args.len(), 4);
            assert_eq!(msg.args, [2, 0, 0, 0].as_ref());
        });
    }

    #[test]
    fn decode_two_messages_gives_expected_result() {
        let mut buf: BytesMut = [
            1u8, 0, 0, 0, 0, 0, 12, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 8, 0,
        ]
        .as_ref()
        .into();

        let mut sut = WaylandCodec::new(Server {}, Family {});
        let _ = sut.decode(&mut buf);
        let result = sut.decode(&mut buf);

        assert_matches!(result, Ok(Some(msg)) => {
            assert_eq!(msg.object_id, ObjectId(1));
            assert_eq!(msg.opcode(), 1);
            assert_eq!(msg.args.len(), 0);
        });
    }
}
