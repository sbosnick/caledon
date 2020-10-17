// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::convert::TryFrom;

use super::{
    ConversionError, Fd, Interface, Message, MessageList, ObjectId, Protocol,
    ProtocolFamily,
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
}

pub enum Requests {
    Destroy(DestroyRequest),
    Conjoin(ConjoinRequest),
}
impl MessageList for Requests {
    type Interface = FdPasser;
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
}

pub enum Events {
    PreFd(PreFdEvent),
    Fd(FdEvent),
}
impl MessageList for Events {
    type Interface = FdPasser;
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
    type InterfaceList = BuildTimeWaylandTests;
}

pub enum BuildTimeWaylandTests {
    FdPasser(FdPasser),
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
    type ProtocolList = Protocols;
}

pub enum Protocols {
    BuildTimeWaylandTests(BuildTimeWaylandTests),
}
impl ProtocolFamily for Protocols {}
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
