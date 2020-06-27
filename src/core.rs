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

use thiserror::Error;

mod codec;
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
#[derive(Debug)]
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

/// A particular [Wayland] message.
///
/// A type implementing `Message` would typically be generated from one of the
/// [Wayland] protocol XML files and would be either a request or an event.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Message: Sized {
    /// The opcode for this message. It uniquely identifies the message type within
    /// the message's `MessageList`.
    const OPCODE: u16;

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
pub trait MessageList {
    /// The interface with which this `MessageList` is associated.
    type Interface: Interface;
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

    /// The interface list to which this interface belongs. This indirectly
    /// identifies the protocol to which this interface belong.
    type InterfaceList: InterfaceList + From<Self> + TryInto<Self>;
}

/// A list of [Wayland] interfaces associated with a particular protocol.
///
/// An `InterfaceList` will typically be an `enum` with each interface for a given
/// protocol associated with one variant of the `enum`. It will typically be
/// generated from one of the [Wayland] protocol XML files.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait InterfaceList {
    /// The protocol with which this `InterfaceList` is associated.
    type Protocol: Protocol;
}

/// The [Wayland] wire protocol representation of a [Wayland] (higher-level) protocol.
///
/// A `Protocol` will typically be generated from a single [Wayland] protocol XML
/// file and consists of a list of the interfaces that make up that protocol.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Protocol: Sized {
    /// The interfaces that make up this `Protocol`.
    type Interfaces: InterfaceList;

    /// The protocol list to which this protocol belongs. This indirectly identifies
    /// the protocol family to which this protocol belongs.
    type ProtocolList: ProtocolList + From<Self> + TryInto<Self>;
}

/// A list of [Wayland] protocols associated with a particular protocol family.
///
/// A `ProtocolList` will typically be an `enum` with each protocol for the protocol
/// family associated with one variant of the `enum`. It will typically be generated
/// when proccessing a collection of [Wayland] protocol XML files.
///
/// `ProtocolList` does not correspondece directly a concept in the [Wayland]
/// protocol but rather is a way of modeling operation on multiple protocols in a
/// unified manner.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait ProtocolList {
    /// The protocol family with which this `ProtocolList` is associated.
    type ProtocolFamily: ProtocolFamily;
}

/// A family of [Wayland] protocols.
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
    /// The protocols associated with this `ProtocolFamily`.
    type Protocols: ProtocolList;
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
#[derive(Debug, Error)]
#[error("Unable to convert a {typ} list to a {typ}.")]
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
    use super::transport::ArgEnqueueFd;
    use std::ffi::CString;

    pub trait ArgumentBase: ArgEncoder + ArgDecoder + ArgEnqueueFd {}

    impl ArgumentBase for i32 {}
    impl ArgumentBase for u32 {}
    impl ArgumentBase for super::Decimal {}
    impl ArgumentBase for CString {}
    impl ArgumentBase for super::ObjectId {}
    impl ArgumentBase for Box<[u8]> {}
    impl ArgumentBase for super::Fd {}

    pub trait SignatureBase: ArgEncoder + ArgDecoder + ArgEnqueueFd {}

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
