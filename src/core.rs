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
/// | fd            | `RawFd`     |
///
/// The `ObjectId` and `Decimal` types are part of this module. The remaining Rust
/// type are part of the standard library.
///
/// This trait is sealed so there cannot be any implementations outside of this
/// crate.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Argument: private::Sealed {}

/// The signature for a [Wayland] message.
///
/// The `Signature` for a message is a collection of the arguments for the message.
/// It would typically be a tuple of `Argument` types. `Signature` is implemented in
/// this crate for tuples up to 32 elements and it is unlikely that other
/// implementations would be necessary (though `Signature` is not sealed should such
/// a need arise).
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait Signature {}

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
    type MessageList: MessageList+From<Self>+TryInto<Self>;
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
    type InterfaceList: InterfaceList+From<Self>+TryInto<Self>;
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
    type ProtocolList: ProtocolList+From<Self>+TryInto<Self>;
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

mod private {
    pub trait Sealed {}
}
