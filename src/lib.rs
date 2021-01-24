// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! A library providing an implementation of the [Wayland] display server protocol.
//!
//! The library provides the [Wayland] wire protocol and abstractions for [Wayland]
//! messages which will be used by code generated from the various [Wayland] protocol
//! XML files.
//!
//! [Wayland]: https://wayland.freedesktop.org/

#![deny(missing_docs, warnings)]

use fd_queue::{DequeueFd, EnqueueFd};
use tokio::io::{AsyncRead, AsyncWrite};

pub mod core;

/// The generated types for the [Wayland] protocol XML files.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub mod protocols {
    include!(concat!(env!("OUT_DIR"), "/protocols.rs"));
}

/// Interface for the underlying communication channel on which the [Wayland]
/// protocol is layered.
///
/// The [Wayland] protocol requires a communication channel that is a bi-directional
/// byte stream that can pass file descriptors. In practice this means Unix domain
/// sockets, but the use of this trait allows the rest of `caledon` to rely on
/// this abstraction.
///
/// This trait is intended to be used as a trait bound and should not be
/// implemented directly. The blanket implementation should be the only
/// implementation of the trait.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub trait IoChannel: AsyncRead + AsyncWrite + EnqueueFd + DequeueFd {}

impl<C> IoChannel for C where C: AsyncWrite + AsyncRead + EnqueueFd + DequeueFd {}
