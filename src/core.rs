// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The [Wayland] wire protocol implementation.
//!
//! [Wayland]: https://wayland.freedesktop.org/

use std::convert::TryInto;
use std::ffi::CString;
use std::fmt;
use std::os::unix::io::{AsRawFd, RawFd};

use snafu::Snafu;

mod codec;
mod dispatch;
mod transport;

/// An argument type for a [Wayland] message.
///
/// The eight arguement types of the wire protocol map to Rust types as follows:
///
/// | Protocol Type | Rust Type   |
/// |---------------|-------------|
/// | int           | `i32`       |
/// | uint          | `u32`       |
/// | fixed         | `Decimal`   |
/// | string        | `CString`   |
/// | object        | `ObjectId`  |
/// | new_id        | `ObjectId`  |
/// | array         | `Box<[u8]>` |
/// | fd            | `Fd`        |
///
/// The `Fd`, `ObjectId` and `Decimal` types are part of this module. The remaining
/// Rust type are part of the standard library.
///
/// This trait is sealed so there cannot be any implementations outside of this
/// crate. The details of the implementation of `Argument` are in the private
/// `ArgumentBase` trait to allow implementation changes without them being breaking
/// changes.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Argument: private::ArgumentBase {}

/// An object or new_id `Argument` for the [Wayland] wire protocol.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ObjectId(u32);

/// A fixed decimal `Argument` for the [Wayland] wire protocol.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Decimal(u32);

/// An fd `Argument` for the [Wayland] wire protocol.
///
/// This is a new-type warpper around a `RawFd`. We can't use `RawFd` directly
/// because that is a type alais for `i32` which is already the int `Argument` type.
#[derive(Debug, Clone)]
pub struct Fd(RawFd);

/// The signature for a [Wayland] message.
///
/// The `Signature` for a message is a collection of the arguments for the message.
/// It would typically be a tuple of `Argument` types. `Signature` is implemented in
/// this crate for tuples up to 12 elements.
///
/// `Signature` is sealed so there cannot be any implementations outside of this
/// crate. The details of the implementation of `Signature` are in the private
/// `SignatureBase` trait to allow implementation change without them being breaking
/// changes.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Signature: private::SignatureBase {}

/// The opcode for a message. It uniquely identifies the message type within the
/// message's `MessageList`.
pub type OpCode = u16;

/// A particular [Wayland] message.
///
/// A type implementing `Message` would typically be generated from one of the
/// [Wayland] protocol XML files and would be either a request or an event.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Message: Sized {
    /// The opcode for this message. It uniquely identifies the message type within
    /// the message's `MessageList`.
    const OPCODE: OpCode;

    /// The signature of the message, that is, the `Argument`s that form the body of
    /// the message.
    type Signature: Signature;

    /// The message list to which this message belongs. It will be either the
    /// list of requests or the list of events for some `Interface`.
    type MessageList: MessageList + From<Self> + TryInto<Self>;

    /// The arguments for this `Message`.
    fn args(&self) -> &Self::Signature;

    /// The object that is sending the `Message`.
    fn sender(&self) -> ObjectId;

    /// Create a new Message given its sender and arguments.
    fn from_signature(sender: ObjectId, args: Self::Signature) -> Self;
}

/// A list of [Wayland] messages associated with a particular interface.
///
/// A `MessageList` will typically be an `enum` with each message type associated
/// with one variant of the `enum` and will typically be generated from one of the
/// [Waland] protocol XML files.
///
/// Each `MessageList` will be either the requests or the events for a particular
/// interface.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait MessageList: Sized {
    /// The interface with which this `MessageList` is associated.
    type Interface: Interface;

    /// Create a new `MessageList` item for the given `OpCode` using the provied
    /// `maker`.
    fn from_opcode<MM: MessageMaker>(
        opcode: OpCode,
        maker: MM,
    ) -> Result<Self, FromOpcodeError<MM::Error>>;
}

/// The possible errors when creating a `MessageList` item from an `OpCode`.
#[derive(Debug, Snafu)]
pub enum FromOpcodeError<E: 'static + std::error::Error> {
    /// The error when the provided `MessageMaker` returns an error.
    #[snafu(display("Unable to make the required message"), context(false))]
    MakerError {
        /// The underlying error from the `MessageMaker`.
        source: E,
    },

    /// The error when the provided `OpCode` is not valid for the given `MessageList`.
    #[snafu(display("Invalid opcode: {}", opcode))]
    InvalidOpcode {
        /// The invalid `OpCode`.
        opcode: OpCode,
    },
}

/// The interface for a type that is able to make a `Message`.
pub trait MessageMaker {
    /// The error type when attepting to make a new `Message`.
    type Error: std::error::Error;

    /// Make a new `Message` of the the provided type.
    fn make<M: Message>(self) -> Result<M, Self::Error>;
}

/// The [Wayland] wire protocol representation of a [Wayland] interface.
///
/// At the wire protocol level an interface is just a list of request messages and a
/// list of event messages. The correspondece of an interface to a protocol object is
/// a higher level concept that is built on top of the wire protocol.
///
/// An `Interface` will typically be generated from one of the [Wayland] protocol XML
/// files.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Interface: Sized {
    /// The list of request messages for this `Interface`.
    type Requests: MessageList;

    /// The list of event message for this `Interface`.
    type Events: MessageList;

    /// The protocol to which this interface belongs.
    type Protocol: Protocol + From<Self> + TryInto<Self>;
}

/// A collection of [Wayland] messages associated with a particular protocol.
///
/// A `ProtocolMessageList` will typically be an `enum` whose variants correspond
/// to a `MessageList` for an interface of the protocol. It will typically be
/// generated from one of the [Wayland] protocol XML files.
///
/// Each `ProtocolMessageList` will be either the requests or the events for the
/// interfaces of a particular protocol.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait ProtocolMessageList {
    /// The protocol to which this message list belongs.
    type Protocol: Protocol;
}

/// The [Wayland] wire protocol representation of a [Wayland] (higher-level) protocol.
///
/// A `Protocol` will typically be an `enum` with each interface for a given
/// protocol associated with one variant of the `enum`. It will typically be
/// generated from one of the [Wayland] protocol XML files.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Protocol: Sized {
    /// A list of the request messages for the interfaces of this `Protocol`.
    type Requests: ProtocolMessageList;

    /// A list of the event messages for the interfaces of this `Protocol`.
    type Events: ProtocolMessageList;

    /// The protocol family to which this protocol belongs.
    type ProtocolFamily: ProtocolFamily + From<Self> + TryInto<Self>;
}

/// A collection of [Wayland] messages associated with a `ProtocolFamily`.
///
/// A `ProtocolFamilyMessageList` will typically be an enum whose variants correspond
/// to a `ProtocolMessageList` for a particular protocol. It will typically be
/// generated from one of the [Wayland] protocol XML files.
///
/// Each `ProtocolFamilyMessageList` will be either the requests or the events for
/// all of the interfaces in all of the protocols in a `ProtocolFamily`.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait ProtocolFamilyMessageList {
    /// The protocol family to which this message list belongs.
    type ProtocolFamily: ProtocolFamily;
}

/// A family of [Wayland] protocols.
///
/// A `ProtocolFamily` will typically be an `enum` with each protocol for the protocol
/// family associated with one variant of the `enum`. It will typically be generated
/// when proccessing a collection of [Wayland] protocol XML files.
///
/// A `ProtocolFamily` is a Rust specific concept that does not correspond directly
/// to a [Wayland] concept. It allows other code to operate on a collection of
/// protocols in a unified manner.
///
/// A `ProtocolFamily` is typically generated when proccessing a collection of
/// [Wayland] protocol XML files.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait ProtocolFamily {
    /// A list of the request messages associated with this `ProtocolFamily`.
    type Requests: ProtocolFamilyMessageList;

    /// A list of the event messages associated with this `ProtocolFamily`.
    type Events: ProtocolFamilyMessageList;
}

// === type alaises and utility traits ===

// Utility to convert a Message type to the Interface type to which it belongs.
// The dead_code warning is a false positive because the type alais is used in
// the generic trait impl below.
#[allow(dead_code)]
type MessageToInterface<T> = <<T as Message>::MessageList as MessageList>::Interface;

// Utility to convert a Message type to the Protocol type to which its Interface belongs.
// The dead_code warning is a false positive because the type alais is used in
// the generic trait impl below.
#[allow(dead_code)]
type MessageToProtocol<T> = <MessageToInterface<T> as Interface>::Protocol;

// Used as a trait bound to enusure a particular message is an event. Should
// not be implemented directly but rather rely on the generic impl below.
trait EventMessage {}

impl<T> EventMessage for T
where
    T: Message,
    MessageToInterface<T>: Interface<Events = T::MessageList>,
{
}

// Used as a trait bound to enusure a particular message is a request. Should
// not be implemented directly but rather rely on the generic impl below.
trait RequestMessage {}

impl<T> RequestMessage for T
where
    T: Message,
    MessageToInterface<T>: Interface<Requests = T::MessageList>,
{
}

// Used as a trait bound to ensure that a particular message comes from an
// interface from a protocol in a particular protocol family. Should not be
// implemented direct but rather rely on the generic impl below.
trait ProtocolFamilyMessage<P> {}

impl<T, P> ProtocolFamilyMessage<P> for T
where
    T: Message,
    P: ProtocolFamily + From<MessageToProtocol<T>> + TryInto<MessageToProtocol<T>>,
    MessageToProtocol<T>: Protocol<ProtocolFamily = P>,
{
}

// === impl Fd ===

impl AsRawFd for &Fd {
    fn as_raw_fd(&self) -> RawFd {
        self.0
    }
}

// === impl ObjectId ===

impl fmt::Display for ObjectId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "object {}", self.0)
    }
}

// === impl Argument ===
impl Argument for i32 {}
impl Argument for u32 {}
impl Argument for Decimal {}
impl Argument for CString {}
impl Argument for ObjectId {}
impl Argument for Box<[u8]> {}
impl Argument for Fd {}

// === impl Signature ===
impl Signature for () {}

macro_rules! tuple_signature_impl {
    ( $($name:ident)+ ) => (
        impl<$($name: Argument),*> Signature for ($($name,)+) {}
    );
}

tuple_signature_impl! { A }
tuple_signature_impl! { A B }
tuple_signature_impl! { A B C }
tuple_signature_impl! { A B C D }
tuple_signature_impl! { A B C D E }
tuple_signature_impl! { A B C D E F }
tuple_signature_impl! { A B C D E F G }
tuple_signature_impl! { A B C D E F G H }
tuple_signature_impl! { A B C D E F G H I }
tuple_signature_impl! { A B C D E F G H I J }
tuple_signature_impl! { A B C D E F G H I J K }
tuple_signature_impl! { A B C D E F G H I J K L }

// === utility types ===
/// An attept to convert from a list type to an item in that list was unsucessful.
///
/// The three list type for which this error might apply are a `MessageList`, an `InterfaceList`,
/// and a `ProtocolList`.
#[derive(Debug, Snafu)]
#[snafu(display("Unable to convert a {} list to a {}.", typ, typ))]
pub struct ConversionError {
    typ: ConversionErrorType,
}

impl ConversionError {
    /// Create a `ConversionError` for a message conversion.
    pub fn message() -> ConversionError {
        ConversionError {
            typ: ConversionErrorType::Message,
        }
    }

    /// Create a `ConversionError` for an interface conversion.
    pub fn interface() -> ConversionError {
        ConversionError {
            typ: ConversionErrorType::Interface,
        }
    }

    /// Create a `ConversionError for a protocol conversion.
    pub fn protocol() -> ConversionError {
        ConversionError {
            typ: ConversionErrorType::Protocol,
        }
    }
}

#[derive(Debug)]
enum ConversionErrorType {
    Message,
    Interface,
    Protocol,
}

impl fmt::Display for ConversionErrorType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ConversionErrorType::*;

        let term = match self {
            Message => "message",
            Interface => "interface",
            Protocol => "protocol",
        };

        write!(f, "{}", term)
    }
}

/// Internal marker trait to allow specializaton of other types to either servers or
/// clients.
pub(crate) trait Role {}

struct ServerRole {}
impl Role for ServerRole {}

struct ClientRole {}
impl Role for ClientRole {}

mod private {
    use super::codec::{ArgDecoder, ArgEncoder};
    use super::transport::{ArgDequeueFd, ArgEnqueueFd};
    use std::ffi::CString;

    pub trait ArgumentBase: ArgEncoder + ArgDecoder + ArgEnqueueFd + ArgDequeueFd {}

    impl ArgumentBase for i32 {}
    impl ArgumentBase for u32 {}
    impl ArgumentBase for super::Decimal {}
    impl ArgumentBase for CString {}
    impl ArgumentBase for super::ObjectId {}
    impl ArgumentBase for Box<[u8]> {}
    impl ArgumentBase for super::Fd {}

    pub trait SignatureBase: ArgEncoder + ArgDecoder + ArgEnqueueFd + ArgDequeueFd {}

    impl SignatureBase for () {}

    macro_rules! tuple_signature_base_impl {
        ( $($name:ident)+ ) => (
            impl<$($name: super::Argument),*> SignatureBase for ($($name,)+) {}
        );
    }

    tuple_signature_base_impl! { A }
    tuple_signature_base_impl! { A B }
    tuple_signature_base_impl! { A B C }
    tuple_signature_base_impl! { A B C D }
    tuple_signature_base_impl! { A B C D E }
    tuple_signature_base_impl! { A B C D E F }
    tuple_signature_base_impl! { A B C D E F G }
    tuple_signature_base_impl! { A B C D E F G H }
    tuple_signature_base_impl! { A B C D E F G H I }
    tuple_signature_base_impl! { A B C D E F G H I J }
    tuple_signature_base_impl! { A B C D E F G H I J K }
    tuple_signature_base_impl! { A B C D E F G H I J K L }
}

#[cfg(test)]
mod testutil;
