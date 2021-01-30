# Overview

This document describes some assumptions that are implicit in the [Wayland]
protocol. With the exception of the last section on gaps, everything here is
intended to be a reflection of a close reading of the protocol, but the
authoritative source of the information is the protocol itself. The gaps section
is written as if it shows gaps in the protocol but should really be understood
as either gaps in the protocol or gaps in my understanding of the protocol.

For the purpose of this document, the [Wayland] protocol is [chapter 4] of the
[specification] and the [wayland.xml] document. This document is focused on the
protocol itself and doesn't describe the architecture that motivates the
protocol. Chapters 1, 2 and 3 of the [specification] do a good job of providing
this background.

[Chapter 4][chapter 4] starts by describing the protocol in the following terms,
"The Wayland protocol is an asynchronous object oriented protocol." The rest of
this document tries to unpack what this means.

[Wayland]: https://wayland.freedesktop.org/
[chapter 4]: https://wayland.freedesktop.org/docs/html/ch04.html
[specification]: https://wayland.freedesktop.org/docs/html/
[wayland.xml]: ../protocol/wayland.xml

# Underlying Communication Channel

The [Wayland] protocol is built on top of an underlying communication channel
that provides a bidirectional byte stream that also supports passing file
descriptors.  In practice this means Unix domain sockets, but the description in
the last sentence describes the implicit assumptions that underlie the protocol.

# Low-level Wire Protocol

The [Wayland] wire protocol that is layered on top of the communication channel
is a framed protocol for passing messages back and forth. The protocol is not
self describing in the sense that it is not possible to decode a message without
carrying some state on the receiving side of the communication channel. The wire
protocol does carry enough information, though to frame the message (that is, to
find the boundary for the end of the current message).

A message identifies a object and an operation on the object and also carries
the arguments for that operation. Decoding the arguments, though, requires
looking up the object in the receiving side's state and then looking up the
operation for the interface implemented by that object. The message itself does
not describe the types of the arguments that it carries.

There are 8 argument types supported by the wire protocol:

* 3 scalar types (signed and unsigned integers, and a fixed decimal type)
* 2 composite types (strings and a byte array)
* 1 type to designate file descriptor passing
* 2 types to identify an object (one for existing objects and one for objects
  being created)

Messages are labeled as either requests (client to sever) or events (server to
client).

# High-level Object Protocol

Layered on top of the wire protocol is a higher level "object" protocol. This is
primarily described in [wayland.xml]. The protocol documents describe the
interfaces that are available for objects to implement, but the objects
themselves are an implicit part of the protocol. They are required by the wire
protocol but are not explicitly defined, except that they implement an
interface.

The message passing is not request/response. That is, requests sent to the
server will not be replied to individually, though generally they will cause the
server to generate some events. There is no necessary correlation, though,
between the "object" generating the request and the "object" generating the
events.

It is possible to conceptualize the "object" in terms of an remote procedure
call protocol. On this conception the client-side holds a proxy to the real
objects which are on the server-side. The proxy then just sends request to the
real object and receives back events. This conceptual model, though, doesn't
really fit well with the object creation semantics that are implicit in the
protocol.

A better conceptual model is that the "object" are abstract "protocol objects"
that span the communication channel. The request and event messages are being
sent between the two sides of the abstract protocol object. On this model the
creation of a new protocol object happens asynchronously: the creation of one
side of the object happens first which generates a creation message. That
creation message then causes the creation of the other side of the object. For
objects that can be destroyed (not all can) the destruction of the objects
happens in a similar manner.

# Object Lifestyles and Lifecycle Messages

A useful way to categorize the abstract protocol objects is by their
"lifestyles", by which I mean the patters of the "lifecycle" messages. A
"lifecycle" message, in tern is a Wayland message that creates or destroys a
protocol object. The lifestyles are at least loosely related to the lifetime of
a protocol object relative to the lifetime of the underlying communication
channel.

## The Ambient Lifestyle

This lifestyle describes a protocol object that is neither created nor
destroyed, it just "is". There is exactly one such object, that is the object
that implements "wl_display". The "display" object implicitly comes into
existence when the underlying communication channel is deemed to be a Wayland
communication channel. Both sides of the channel then just assume the existence
of the display object and the display object continues to exist until the
communication channel is shut down.

## The Global Binding Lifestyle

This lifestyle describes protocol objects that are created when a client binds
to a global object on the server. The global objects on the server are the
registry and the objects described by the registry. It would be tempting to
treat these global objects as the targets of a remote procedure call interface
in which the client-side representations are proxy objects. This conceptual
model, though, is not consistent with the message passing that leads to being
able to access the global object.

A more consistent conceptual model is to treat the binding to the global object
as the "protocol object" that spans the connection. These bindings are initially
created on the client through a "binding" request. Some, but not all, of the
resulting "binding" objects have a destructor (a request that is marked with
_type="destructor"_) for destroying the binding. If a binding object does not
have such a destructor then it will exist until the underlying communication
channel is shut down. For such binding objects it is possible to create more
than one binding to the same global object but this is probably a bad idea.

In the core [wayland.xml] document the following interfaces describe objects
that have the global binding lifestyle: wl_registry, wl_compositor, wl_shm,
wl_data_device, wl_shell (deprecated), wl_seat, wl_output, and wl_subcompositor.
These interfaces (with the exception of wl_registry) can be identified in
[wayland.xml] by the lack of a factory request on some other objects.

Many of the binding objects are themselves abstract factories for creating other
protocol objects. These objects are also the root of the versioning scheme for
the [Wayland] protocol (with the exception of the wl_registry binding object
which cannot be versioned).

## The Dependant Lifestyle

This lifestyle describes protocol objects that are created through a request
message on an abstract factory, typically a binding object to a global singleton
object. The manipulation of these objects is in many ways the whole point of the
[Wayland] protocol.

Almost all protocol object with the dependent lifestyle have a destructor (a
request marked with _type="destructor"_) for destroying the protocol object
though it may have been added to the protocol after its initial release. If a
protocol object does not have a destructor then (typically) it is destroyed in
conjunction with the destruction of some other protocol object. In the core
[wayland.xml] document the only such protocol object an object with the
deprecated wl_shell_surface interface.

In the core [wayland.xml] document objects with the following interfaces have
the dependent lifestyle: wl_surface, wl_region, wl_buffer, wl_shm_pool,
wl_data_offer, wl_data_source, wl_data_device, wl_shell_surface (deprecated),
wl_pointer, wl_keyboard, wl_touch, wl_subsurface.

## The Ephemeral Lifestyle

This lifestyle describes a protocol object that is created through a request
message but destroyed through the operation of an event. In the core
[wayland.xml] document there is exactly one object with the ephemeral lifestyle:
an object that implements the wl_callback interface. A callback object is
created by either wl_display::sync or wl_surface::frame and that callback object
is implicitly destroyed as a part of its done event.

# Gaps

This section of the document describes gaps in either a) my underlying of the
[Wayland] protocol or b) in the [specification] itself (namely [chapter 4] and
[wayland.xml]). Where an investigation of the c code in Weston or in libwayland
gives some clarification then that information is also listed.

## Object ID for the Messages on the wl_display Ambient Object
The display object (i.e. the protocol object that implements wl_display) has an
ambient lifestyle. There is no factory message that creates the display object,
it just "is". The implication of this is that the object id for the headers of
the messages on the display object must be agreed to in advance but neither
[chapter 4] nor [wayland.xml] say what object_id is assigned to the display
object.

libwayland appears to assigned the object id 1 to the display object so this
appears to be the value that is agreed to in advance.

## Object ID for the Output Argument on wl_surface::enter/leave

The document for wl_surface::enter and wl_surface::leave in [wayland.xml]
doesn't specify where the object id used to identify the output argument comes
from.

The reference implementation, Weston, though makes it clear that the object id
for the output argument is the one that was previously used in a call to
wl_registry::bind.
