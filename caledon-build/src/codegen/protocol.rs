// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::model::{Documentation, Interface, Protocol};

use super::{
    doc::{format_long_doc, format_short_doc},
    generate_interface,
};
use proc_macro2::TokenStream;
use quote::quote;

pub(super) fn generate_protocol(protocol: &Protocol) -> TokenStream {
    let mod_ident = protocol.mod_ident();
    let enum_entry_ident = protocol.enum_entry_ident();
    let mod_doc = format_long_doc(protocol, |name| {
        format!("Caledon types for the {} protocol.", name)
    });
    let protocol_doc = format!("The {} protocol.", protocol.name());
    let protocol_requests_doc = format!("The requests for the {} protocol.", protocol.name());
    let protocol_events_doc = format!("The events for the {} protocol.", protocol.name());
    let entries = protocol.interfaces().map(generate_interface_entry);
    let request_entries = protocol.interfaces().map(generate_protocol_request_entry);
    let event_entries = protocol.interfaces().map(generate_protocol_event_entry);
    let interfaces = protocol.interfaces().map(|i| generate_interface(i));

    quote! {
        #[allow(clippy::too_many_arguments)]
        #[doc = #mod_doc]
        pub mod #mod_ident {
            use std::convert::TryFrom;

            #[allow(unused_imports)]
            use std::ffi::CString;

            use crate::core::{self, Interface, ObjectId, ProtocolMessageList};

            #[allow(unused_imports)]
            use crate::core::{Decimal, Fd};

            #[doc = #protocol_doc]
            #[derive(Debug, PartialEq)]
            pub enum Protocol {
                #(#entries,)*
            }

            #[doc = #protocol_requests_doc]
            #[derive(Debug, PartialEq)]
            pub enum Requests {
                #(#request_entries,)*
            }

            #[doc = #protocol_events_doc]
            #[derive(Debug, PartialEq)]
            pub enum Events {
                #(#event_entries,)*
            }

            impl core::Protocol for Protocol {
                type Requests = Requests;
                type Events = Events;

                type ProtocolFamily = super::Protocols;
            }

            impl From<Protocol> for super::Protocols {
                fn from(t: Protocol) -> Self {
                    Self::#enum_entry_ident(t)
                }
            }

            impl TryFrom<super::Protocols> for Protocol {
                type Error = crate::core::ConversionError;

                fn try_from(p: super::Protocols) -> Result<Self, Self::Error> {
                    #[allow(unreachable_patterns)]
                    match p {
                        super::Protocols::#enum_entry_ident(inner) => Ok(inner),
                        _ => Err(crate::core::ConversionError::protocol()),
                    }
                }
            }

            impl ProtocolMessageList for Requests {
                type Protocol = Protocol;
            }

            impl ProtocolMessageList for Events {
                type  Protocol = Protocol;
            }

            #(#interfaces)*
        }
    }
}

fn generate_interface_entry(interface: &Interface) -> TokenStream {
    let entry = interface.enum_entry_ident();
    let interface_ident = interface.interface_ident();
    let entry_doc = format_short_doc(interface, |name| format!("The {} interface.", name));

    quote! {
        #[doc = #entry_doc]
        #entry(#interface_ident)
    }
}

fn generate_protocol_request_entry(interface: &Interface) -> TokenStream {
    let entry = interface.enum_entry_ident();
    let entry_doc = format_short_doc(interface, |name| {
        format!("The requests for the {} interface.", name)
    });
    let mod_ident = interface.mod_ident();

    quote! {
        #[doc = #entry_doc]
        #entry(#mod_ident::Requests)
    }
}

fn generate_protocol_event_entry(interface: &Interface) -> TokenStream {
    let entry = interface.enum_entry_ident();
    let entry_doc = format_short_doc(interface, |name| {
        format!("The events for the {} interface.", name)
    });
    let mod_ident = interface.mod_ident();

    quote! {
        #[doc = #entry_doc]
        #entry(#mod_ident::Events)
    }
}
