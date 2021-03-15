// Copyright 2021 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The client side of the higher level [Wayland] object protocol.
//!
//! [Wayland]: https://wayland.freedesktop.org/

use std::{convert::TryInto, error, fmt, iter::FromIterator, marker::PhantomData, sync::Arc};

use futures_core::Stream;
use futures_sink::Sink;
use futures_util::{future, sink::SinkExt, stream::TryStreamExt};
use snafu::{IntoError, ResultExt, Snafu};

use crate::{
    core::{
        make_wire_protocol, ClientRole, Message, ObjectId, ProtocolFamily, WaylandState, WireError,
        WireRecv, WireSend, WireState,
    },
    protocols::{
        self,
        wayland::{WlCallback, WlDisplay, WlRegistry},
    },
    registry::{Global, Registry},
    IoChannel,
};

/// The core client-side object to access a [Wayland] server.
///
/// [Wayland]: https://wayland.freedesktop.org/
pub struct Display<T> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    inner: DisplayImpl<ClientSend<T>, ClientRecv<T>, ClientState, WireError>,
}

type ClientSend<T> = WireSend<T, ClientRole, protocols::Protocols>;
type ClientRecv<T> = WireRecv<T, ClientRole, protocols::Protocols>;
type ClientState = WireState<ClientRole, protocols::Protocols>;

impl<T> Display<T>
where
    T: IoChannel + Unpin,
{
    /// Create a new `Display`.
    pub async fn new(channel: T) -> Result<Self, ClientError> {
        let (send, recv, state) = make_wire_protocol(channel);

        Ok(Display {
            inner: DisplayImpl::new(send, recv, state).await?,
        })
    }

    /// Dispatch incoming event messages.
    ///
    /// This method resolves with either a fatal error on the channel or if the
    /// stream of event messages reaches the end.
    pub async fn dispatch(&self) -> Result<(), ClientError> {
        todo!();
    }
}

/// The possible errors arising in the core client-side [Wayland] objects.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug, Snafu)]
pub struct ClientError(ClientErrorImpl<WireError>);

#[derive(Debug, Snafu)]
enum ClientErrorImpl<E: error::Error + 'static> {
    #[snafu(display("Error with the underlying communication channel during the {}", phase))]
    Transport { source: E, phase: ClientPhase },

    #[snafu(display("Fatal protocol error with the Wayland protocol during the {}", phase))]
    Protocol { phase: ClientPhase },
}

#[derive(Debug, Clone, Copy)]
enum ClientPhase {
    InitialHandshake,
}

impl fmt::Display for ClientPhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ClientPhase::*;
        match self {
            InitialHandshake => write!(f, "initial handshake"),
        }
    }
}

struct DisplayImpl<Si, St, WS, E> {
    // TODO: remove this when it is no longer needed
    #[allow(dead_code)]
    registry: Registry,
    _phantom: PhantomData<(Si, St, WS, E)>,
}

impl<Si, St, WS, E> DisplayImpl<Si, St, WS, E>
where
    Si: Sink<protocols::Requests, Error = E> + Unpin,
    St: Stream<Item = Result<protocols::Events, E>> + Unpin,
    WS: WaylandState<protocols::Protocols, Error = E>,
    E: error::Error + 'static,
{
    async fn new(mut send: Si, mut recv: St, state: WS) -> Result<Self, ClientErrorImpl<E>> {
        let phase = ClientPhase::InitialHandshake;

        let display = create_object(&state, |id| WlDisplay::new(id))?;
        let d = get_display(&display);
        let registry = create_object(&state, |id| WlRegistry::new(id))?;
        let r_id = registry.id();
        let callback = create_object(&state, |id| WlCallback::new(id))?;
        let c_id = callback.id();

        feed_wayland(&mut send, d.get_registry_request(r_id).into(), phase).await?;
        feed_wayland(&mut send, d.sync_request(c_id).into(), phase).await?;
        send.flush().await.context(Transport { phase })?;

        let globals = (&mut recv)
            .try_take_while(|item| future::ok(!is_done(item)))
            .map_err(|e| Transport { phase }.into_error(e))
            .try_fold(Vec::new(), |mut g, i| {
                extract_global(&i).map_or_else(
                    || future::err(Protocol { phase }.build()),
                    |global| {
                        g.push(global);
                        future::ok(g)
                    },
                )
            })
            .await?;

        Ok(Self {
            registry: Registry::from_iter(globals),
            _phantom: PhantomData,
        })
    }
}

fn create_object<WS, F, I, E>(
    state: &WS,
    f: F,
) -> Result<Arc<protocols::Protocols>, ClientErrorImpl<E>>
where
    WS: WaylandState<protocols::Protocols, Error = E>,
    E: error::Error,
    F: Fn(ObjectId) -> I,
    I: Into<protocols::wayland::Protocol>,
{
    use protocols::Protocols::Wayland;
    let phase = ClientPhase::InitialHandshake;

    state
        .create_object(|id| Wayland(f(id).into()))
        .context(Transport { phase })
}

async fn feed_wayland<S, E>(
    sink: &mut S,
    request: protocols::wayland::Requests,
    phase: ClientPhase,
) -> Result<(), ClientErrorImpl<E>>
where
    S: Sink<protocols::Requests, Error = E> + Unpin,
    E: error::Error + 'static,
{
    use protocols::Requests::Wayland;

    sink.feed(Wayland(request))
        .await
        .context(Transport { phase })
}

fn get_display(display: &protocols::Protocols) -> &protocols::wayland::WlDisplay {
    use protocols::wayland::Protocol;

    display
        .try_into()
        .and_then(|w: &Protocol| w.try_into())
        .expect("get_display called on non-display object")
}

fn is_done(event: &protocols::Events) -> bool {
    use protocols::wayland::wl_callback::Events::Done;
    use protocols::wayland::Events::WlCallback;
    use protocols::Events::Wayland;

    if let Wayland(WlCallback(Done(_))) = event {
        true
    } else {
        false
    }
}

fn extract_global(event: &protocols::Events) -> Option<(u32, Global)> {
    use protocols::wayland::wl_registry::Events::Global as RegGlobal;
    use protocols::wayland::Events::WlRegistry;
    use protocols::Events::Wayland;

    if let Wayland(WlRegistry(RegGlobal(g))) = event {
        let (name, interface, version) = g.args();
        Some((*name, Global::new(interface.clone(), *version)))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use std::{
        ffi::CString,
        sync::{
            atomic::{AtomicU32, Ordering},
            Arc,
        },
    };

    use futures::{channel::mpsc, prelude::*, stream};

    use crate::core::{testutil::new_object_id, ObjectId};

    #[derive(Debug, Snafu)]
    struct StubError;

    #[derive(Default)]
    struct StubState {
        next: AtomicU32,
    }

    impl WaylandState<protocols::Protocols> for StubState {
        type Error = StubError;

        fn create_object(
            &self,
            f: impl Fn(ObjectId) -> protocols::Protocols,
        ) -> Result<std::sync::Arc<protocols::Protocols>, StubError> {
            Ok(Arc::new(f(new_object_id(
                self.next.fetch_add(1, Ordering::SeqCst) + 1,
            ))))
        }

        fn add_remote_object(&self, _id: ObjectId, _object: protocols::Protocols) {}

        fn remove_object(&self, _id: ObjectId) {}
    }

    #[tokio::test]
    async fn display_impl_new_sends_initial_requests() {
        use protocols::wayland::wl_callback::DoneEvent;
        use protocols::wayland::wl_display::{GetRegistryRequest, SyncRequest};
        use protocols::Events::Wayland as WE;
        use protocols::Requests::Wayland as WR;
        let state = StubState::default();
        let (send, recv) = mpsc::channel(10);
        let send = send.sink_map_err(|_| StubError);

        DisplayImpl::new(
            send,
            stream::once(future::ok(WE(DoneEvent::new(new_object_id(3), 0).into()))),
            state,
        )
        .await
        .expect("Error creating DisplayImpl.");
        let result: Vec<_> = recv.take(2).collect().await;

        assert_eq!(
            result,
            vec![
                WR(GetRegistryRequest::new(new_object_id(1), new_object_id(2)).into()),
                WR(SyncRequest::new(new_object_id(1), new_object_id(3)).into()),
            ]
        );
    }

    #[tokio::test]
    async fn display_impl_new_recvies_initial_events() {
        use protocols::wayland::{wl_callback::DoneEvent, wl_registry::GlobalEvent};
        use protocols::Events::Wayland;
        let interface = CString::new("wl_compositor").expect("Can't create interface name");
        let state = StubState::default();
        let recv = stream::iter(
            vec![
                Ok(Wayland(
                    GlobalEvent::new(new_object_id(2), 1, interface, 1).into(),
                )),
                Ok(Wayland(DoneEvent::new(new_object_id(3), 0).into())),
            ]
            .into_iter(),
        );

        let result = DisplayImpl::new(sink::drain().sink_map_err(|_| StubError), recv, state).await;

        assert!(result.is_ok());
    }
}
