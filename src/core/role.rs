// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! Marker trait and associed blanket traits and type functions to specialization the behaviour
//! of other types for servers or for clients.

use super::{FromOpcodeError, MessageMaker, OpCode, ProtocolFamily, ProtocolFamilyMessageList};

/// Internal marker trait to allow specializaton of other types to either servers or
/// clients.
pub trait Role {}

#[derive(Debug)]
pub(crate) struct ServerRole {}
impl Role for ServerRole {}

#[derive(Debug)]
pub(crate) struct ClientRole {}
impl Role for ClientRole {}

/// Blanket trait for checking if a given [ProtocolFamily] passes a file descriptor on a particular
/// message.
///
/// This is specialized for [ServerRole] and [ClientRole] and those should be the only
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

/// Blanket trait for making a message for the given [ProtocolFamily] element given the opcode for
/// that message.
///
/// This is specialized for [ServerRole] and [ClientRole] and those should be the only
/// implementations of this trait. This trait is otherwise intended to be used as a trait bound.
pub(crate) trait MakeMessage<R: Role> {
    type Output: ProtocolFamilyMessageList;

    fn make_message<MM: MessageMaker>(
        &self,
        opcode: OpCode,
        msg: MM,
    ) -> Result<Self::Output, FromOpcodeError<MM::Error>>;
}

impl<PF> MakeMessage<ServerRole> for PF
where
    PF: ProtocolFamily,
{
    type Output = PF::Requests;

    fn make_message<MM: MessageMaker>(
        &self,
        opcode: OpCode,
        msg: MM,
    ) -> Result<Self::Output, FromOpcodeError<MM::Error>> {
        self.make_request_message(opcode, msg)
    }
}

impl<PF> MakeMessage<ClientRole> for PF
where
    PF: ProtocolFamily,
{
    type Output = PF::Events;

    fn make_message<MM: MessageMaker>(
        &self,
        opcode: OpCode,
        msg: MM,
    ) -> Result<Self::Output, FromOpcodeError<MM::Error>> {
        self.make_event_message(opcode, msg)
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

/// A type function to select the type of messages to receive for a [ProtocolFamily] depending on
/// the [Role].
pub trait RecvMsg<R: Role> {
    type Output: ProtocolFamilyMessageList;
}

impl<PF: ProtocolFamily> RecvMsg<ServerRole> for PF {
    type Output = PF::Requests;
}

impl<PF: ProtocolFamily> RecvMsg<ClientRole> for PF {
    type Output = PF::Events;
}

/// Type alias to make using the [RecvMsg] type function easier.
pub(crate) type RecvMsgType<R, P> = <P as RecvMsg<R>>::Output;
