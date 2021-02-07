// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! Marker trait and associed blanket traits and type functions to specialization the behaviour
//! of other types for servers or for clients.

use super::{OpCode, ProtocolFamily, ProtocolFamilyMessageList};

/// Internal marker trait to allow specializaton of other types to either servers or
/// clients.
pub trait Role {}

pub(crate) struct ServerRole {}
impl Role for ServerRole {}

pub(crate) struct ClientRole {}
impl Role for ClientRole {}

/// Blanket trait for checking if a given [ProtocolFamily] passes a file descriptor on a particular
/// message.
///
/// This is specializaton for [ServerRole] and [ClientRole] and those should be the only
/// implementations of this trait. This trait is otherwise intened to be used as a trait bound.
pub(crate) trait HasFd<R: Role> {
    fn has_fd(&self, opcode: OpCode) -> bool;
}

impl<PF> HasFd<ServerRole> for PF
where
    PF: ProtocolFamily,
{
    fn has_fd(&self, opcode: OpCode) -> bool {
        self.event_has_fd(opcode)
    }
}

impl<PF> HasFd<ClientRole> for PF
where
    PF: ProtocolFamily,
{
    fn has_fd(&self, opcode: OpCode) -> bool {
        self.request_has_fd(opcode)
    }
}

/// A type function to select the type of messages to send for a [ProtocolFamily] depending on the
/// [Role].
pub trait SendMsg<R: Role> {
    type Output: ProtocolFamilyMessageList;
}

impl<PF: ProtocolFamily> SendMsg<ServerRole> for PF {
    type Output = PF::Events;
}

impl<PF: ProtocolFamily> SendMsg<ClientRole> for PF {
    type Output = PF::Requests;
}

/// Type alias to make using the [SendMsg] type function easier.
pub(crate) type SendMsgType<R, P> = <P as SendMsg<R>>::Output;

