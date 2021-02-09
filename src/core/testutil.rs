// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::convert::TryFrom;

use super::{
    ConversionError, Fd, FromOpcodeError, Interface, Message, MessageList, ObjectId, Protocol,
    ProtocolFamily, ProtocolFamilyMessageList, ProtocolMessageList,
};

// These types are a manual implementation of the "build_time_wayland_tests" protocol from the
// Wayland repository (in the "protocol/tests.xml" file).

pub struct DestroyRequest {}
impl Message for DestroyRequest {
    const OPCODE: u16 = 0;
    type Signature = ();
    type MessageList = Requests;

    fn args(&self) -> &Self::Signature {
        &()
    }

    fn sender(&self) -> ObjectId {
        ObjectId(1)
    }

    fn from_signature(_sender: ObjectId, _args: Self::Signature) -> Self {
        Self {}
    }
}

pub struct ConjoinRequest {}
impl Message for ConjoinRequest {
    const OPCODE: u16 = 1;
    type Signature = (ObjectId,);
    type MessageList = Requests;

    fn args(&self) -> &Self::Signature {
        static FIXED_ARGS: (ObjectId,) = (ObjectId(2),);
        &FIXED_ARGS
    }

    fn sender(&self) -> ObjectId {
        ObjectId(1)
    }

    fn from_signature(_sender: ObjectId, _args: Self::Signature) -> Self {
        Self {}
    }
}

pub enum Requests {
    Destroy(DestroyRequest),
    Conjoin(ConjoinRequest),
}
impl MessageList for Requests {
    type Interface = FdPasser;

    fn from_opcode<MM>(opcode: super::OpCode, maker: MM) -> Result<Self, FromOpcodeError<MM::Error>>
    where
        MM: super::MessageMaker,
    {
        let item = match opcode {
            0 => maker.make::<DestroyRequest>().map(|m| m.into())?,
            1 => maker.make::<ConjoinRequest>().map(|m| m.into())?,
            _ => panic!("Unknown opcode"),
        };

        Ok(item)
    }

    fn has_fd(_opcode: super::OpCode) -> bool {
        false
    }
}
impl From<DestroyRequest> for Requests {
    fn from(d: DestroyRequest) -> Self {
        Requests::Destroy(d)
    }
}
impl TryFrom<Requests> for DestroyRequest {
    type Error = ConversionError;

    fn try_from(r: Requests) -> Result<Self, Self::Error> {
        match r {
            Requests::Destroy(d) => Ok(d),
            _ => Err(ConversionError::message()),
        }
    }
}
impl From<ConjoinRequest> for Requests {
    fn from(c: ConjoinRequest) -> Self {
        Requests::Conjoin(c)
    }
}
impl TryFrom<Requests> for ConjoinRequest {
    type Error = ConversionError;

    fn try_from(r: Requests) -> Result<Self, Self::Error> {
        match r {
            Requests::Conjoin(c) => Ok(c),
            _ => Err(ConversionError::message()),
        }
    }
}

pub struct PreFdEvent {}
impl Message for PreFdEvent {
    const OPCODE: u16 = 0;
    type Signature = ();
    type MessageList = Events;

    fn args(&self) -> &Self::Signature {
        &()
    }

    fn sender(&self) -> ObjectId {
        ObjectId(1)
    }

    fn from_signature(_sender: ObjectId, _args: Self::Signature) -> Self {
        Self {}
    }
}

pub struct FdEvent {
    sender: ObjectId,
    args: (Fd,),
}
impl FdEvent {
    pub fn new(sender: ObjectId, fd: Fd) -> Self {
        Self {
            sender,
            args: (fd,),
        }
    }
}
impl Message for FdEvent {
    const OPCODE: u16 = 1;
    type Signature = (Fd,);
    type MessageList = Events;

    fn args(&self) -> &Self::Signature {
        &self.args
    }

    fn sender(&self) -> ObjectId {
        self.sender
    }

    fn from_signature(sender: ObjectId, args: Self::Signature) -> Self {
        Self { sender, args }
    }
}

pub enum Events {
    PreFd(PreFdEvent),
    Fd(FdEvent),
}
impl MessageList for Events {
    type Interface = FdPasser;

    fn from_opcode<MM>(opcode: super::OpCode, maker: MM) -> Result<Self, FromOpcodeError<MM::Error>>
    where
        MM: super::MessageMaker,
    {
        let item = match opcode {
            0 => maker.make::<PreFdEvent>().map(|m| m.into())?,
            1 => maker.make::<FdEvent>().map(|m| m.into())?,
            _ => panic!("Unknown opcode"),
        };

        Ok(item)
    }

    fn has_fd(opcode: super::OpCode) -> bool {
        match opcode {
            0 => false,
            1 => true,
            _ => panic!("Unknown opcode"),
        }
    }
}
impl From<PreFdEvent> for Events {
    fn from(p: PreFdEvent) -> Self {
        Events::PreFd(p)
    }
}
impl TryFrom<Events> for PreFdEvent {
    type Error = ConversionError;
    fn try_from(e: Events) -> Result<Self, Self::Error> {
        match e {
            Events::PreFd(p) => Ok(p),
            _ => Err(ConversionError::message()),
        }
    }
}
impl From<FdEvent> for Events {
    fn from(f: FdEvent) -> Self {
        Events::Fd(f)
    }
}
impl TryFrom<Events> for FdEvent {
    type Error = ConversionError;
    fn try_from(e: Events) -> Result<Self, Self::Error> {
        match e {
            Events::Fd(f) => Ok(f),
            _ => Err(ConversionError::message()),
        }
    }
}

pub struct FdPasser {}
impl Interface for FdPasser {
    type Requests = Requests;
    type Events = Events;
    type Protocol = BuildTimeWaylandTests;
}

pub enum BuildTimeWaylandTests {
    FdPasser(FdPasser),
}
#[allow(dead_code)]
pub enum BuildTimeWaylandTestsRequest {
    FdPasser(Requests),
}
#[allow(dead_code)]
pub enum BuildTimeWaylandTestsEvents {
    FdPasser(Events),
}
impl From<FdPasser> for BuildTimeWaylandTests {
    fn from(f: FdPasser) -> Self {
        Self::FdPasser(f)
    }
}
impl TryFrom<BuildTimeWaylandTests> for FdPasser {
    type Error = ();

    fn try_from(i: BuildTimeWaylandTests) -> Result<Self, Self::Error> {
        match i {
            BuildTimeWaylandTests::FdPasser(f) => Ok(f),
        }
    }
}
impl Protocol for BuildTimeWaylandTests {
    type Requests = BuildTimeWaylandTestsRequest;

    type Events = BuildTimeWaylandTestsEvents;

    type ProtocolFamily = Protocols;
}
impl ProtocolMessageList for BuildTimeWaylandTestsRequest {
    type Protocol = BuildTimeWaylandTests;
}
impl ProtocolMessageList for BuildTimeWaylandTestsEvents {
    type Protocol = BuildTimeWaylandTests;
}

pub enum Protocols {
    BuildTimeWaylandTests(BuildTimeWaylandTests),
}
#[allow(dead_code)]
pub enum FamilyRequests {
    BuildTimeWaylandTests(BuildTimeWaylandTestsRequest),
}
#[allow(dead_code)]
pub enum FamilyEvents {
    BuildTimeWaylandTests(BuildTimeWaylandTestsEvents),
}
impl ProtocolFamily for Protocols {
    type Requests = FamilyRequests;

    type Events = FamilyEvents;

    fn request_has_fd(&self, opcode: super::OpCode) -> bool {
        match self {
            Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(_)) => {
                <FdPasser as Interface>::Requests::has_fd(opcode)
            }
        }
    }

    fn event_has_fd(&self, opcode: super::OpCode) -> bool {
        match self {
            Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(_)) => {
                <FdPasser as Interface>::Events::has_fd(opcode)
            }
        }
    }

    fn make_request_message<MM: super::MessageMaker>(
        &self,
        opcode: super::OpCode,
        msg: MM,
    ) -> Result<Self::Requests, FromOpcodeError<MM::Error>> {
        match self {
            Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(_)) => {
                <FdPasser as Interface>::Requests::from_opcode(opcode, msg).map(|m| {
                    FamilyRequests::BuildTimeWaylandTests(BuildTimeWaylandTestsRequest::FdPasser(m))
                })
            }
        }
    }

    fn make_event_message<MM: super::MessageMaker>(
        &self,
        opcode: super::OpCode,
        msg: MM,
    ) -> Result<Self::Events, FromOpcodeError<MM::Error>> {
        match self {
            Protocols::BuildTimeWaylandTests(BuildTimeWaylandTests::FdPasser(_)) => {
                <FdPasser as Interface>::Events::from_opcode(opcode, msg).map(|m| {
                    FamilyEvents::BuildTimeWaylandTests(BuildTimeWaylandTestsEvents::FdPasser(m))
                })
            }
        }
    }
}
impl From<BuildTimeWaylandTests> for Protocols {
    fn from(b: BuildTimeWaylandTests) -> Self {
        Protocols::BuildTimeWaylandTests(b)
    }
}
impl TryFrom<Protocols> for BuildTimeWaylandTests {
    type Error = ();

    fn try_from(p: Protocols) -> Result<Self, Self::Error> {
        match p {
            Protocols::BuildTimeWaylandTests(b) => Ok(b),
        }
    }
}
impl ProtocolFamilyMessageList for FamilyRequests {
    type ProtocolFamily = Protocols;

    fn handle_message<MH: super::MessageHandler>(&self, mut handler: MH) -> Result<(), MH::Error> {
        use BuildTimeWaylandTestsRequest::FdPasser;
        use FamilyRequests::BuildTimeWaylandTests;
        use Requests::{Conjoin, Destroy};

        match self {
            BuildTimeWaylandTests(FdPasser(Destroy(msg))) => handler.handle(msg),
            BuildTimeWaylandTests(FdPasser(Conjoin(msg))) => handler.handle(msg),
        }
    }
}
impl ProtocolFamilyMessageList for FamilyEvents {
    type ProtocolFamily = Protocols;

    fn handle_message<MH: super::MessageHandler>(&self, mut handler: MH) -> Result<(), MH::Error> {
        use BuildTimeWaylandTestsEvents::FdPasser;
        use Events::{Fd, PreFd};
        use FamilyEvents::BuildTimeWaylandTests;

        match self {
            BuildTimeWaylandTests(FdPasser(PreFd(msg))) => handler.handle(msg),
            BuildTimeWaylandTests(FdPasser(Fd(msg))) => handler.handle(msg),
        }
    }
}
