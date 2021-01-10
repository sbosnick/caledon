// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::convert::TryInto;

use proc_macro2::{Ident, TokenStream};

use crate::model::{Args, Documentation, Event, Interface, Message, Request};
use quote::quote;

use super::{
    doc::{format_long_doc, format_message_new_doc, format_short_doc},
    generate_event, generate_new_param, generate_request,
};

pub(super) fn generate_interface(interface: &Interface, interface_list: &Ident) -> TokenStream {
    let enum_entry_ident = interface.enum_entry_ident();
    let interface_ident = interface.interface_ident();
    let interface_doc = format_long_doc(interface, |name| format!("The {} interface.", name));
    let mod_ident = interface.mod_ident();
    let mod_doc = format!("The messages for the {} interface.", interface.name());
    let req_doc = format!("The requests for the {} interface.", interface.name());
    let evt_doc = format!("The events for the {} interface.", interface.name());
    let new_doc = format!("Create a new {}.", interface_ident);
    let request_entries = interface.requests().map(generate_request_entry);
    let requests = interface.requests().enumerate().map(generate_request);
    let request_factories = interface
        .requests()
        .map(|r| generate_request_factory(r, &mod_ident));
    let request_from_opcode_entries = interface
        .requests()
        .enumerate()
        .map(generate_request_from_op_entry);
    let request_has_fd_entries = interface.requests().enumerate().map(generate_has_fd_entry);
    let event_entries = interface.events().map(generate_event_entry);
    let events = interface.events().enumerate().map(generate_event);
    let event_factories = interface
        .events()
        .map(|e| generate_event_factory(e, &mod_ident));
    let event_from_opcode_entries = interface
        .events()
        .enumerate()
        .map(generate_event_from_op_entry);
    let event_has_fd_entries = interface.events().enumerate().map(generate_has_fd_entry);

    quote! {
        #[doc = #interface_doc]
        pub struct #interface_ident {
            id: ObjectId,
        }

        impl #interface_ident {
            #[doc = #new_doc]
            pub fn new(id: ObjectId) -> Self {
                Self { id }
            }

            #(#request_factories)*

            #(#event_factories)*
        }

        impl Interface for #interface_ident {
            type Requests = #mod_ident::Requests;
            type Events = #mod_ident::Events;
            type Protocol = #interface_list;
        }

        impl From<#interface_ident> for #interface_list {
            fn from(t: #interface_ident) -> Self {
                Self::#enum_entry_ident(t)
            }
        }

        impl TryFrom<#interface_list> for #interface_ident {
            type Error = crate::core::ConversionError;

            fn try_from(i: #interface_list) -> Result<Self, Self::Error> {
                #[allow(unreachable_patterns)]
                match i {
                    #interface_list::#enum_entry_ident(inner) => Ok(inner),
                    _ => Err(crate::core::ConversionError::interface()),
                }
            }
        }

        #[doc = #mod_doc]
        pub mod #mod_ident {
            use std::convert::TryFrom;

            #[allow(unused_imports)]
            use std::ffi::CString;

            use crate::core::{FromOpcodeError, Message, MessageList, MessageMaker, ObjectId, OpCode};

            #[allow(unused_imports)]
            use crate::core::{Decimal, Fd};

            #[doc = #req_doc]
            pub enum Requests {
                #(#request_entries,)*
            }

            impl MessageList for Requests {
                type Interface = super::#interface_ident;

                #[allow(unused_variables, unused_mut, clippy::match_single_binding)]
                fn from_opcode<MM: MessageMaker>(opcode: OpCode, mut maker: MM) -> Result<Self, FromOpcodeError<MM::Error>> {
                    let item = match opcode {
                        #(#request_from_opcode_entries)*
                        _ => return Err(FromOpcodeError::InvalidOpcode{opcode}),
                    };

                    #[allow(unreachable_code)]
                    Ok(item)
                }

                #[allow(clippy::match_single_binding, clippy::match_like_matches_macro)]
                fn has_fd(opcode: OpCode) -> bool {
                    match opcode {
                        #(#request_has_fd_entries)*
                        _ => false,
                    }
                }
            }

            #[doc = #evt_doc]
            pub enum Events {
                #(#event_entries,)*
            }

            impl MessageList for Events {
                type Interface = super::#interface_ident;

                #[allow(unused_variables, unused_mut, clippy::match_single_binding)]
                fn from_opcode<MM: MessageMaker>(opcode: OpCode, mut maker: MM) -> Result<Self, FromOpcodeError<MM::Error>> {
                    let item = match opcode {
                        #(#event_from_opcode_entries)*
                        _ => return Err(FromOpcodeError::InvalidOpcode{opcode}),
                    };

                    #[allow(unreachable_code)]
                    Ok(item)
                 }

                #[allow(clippy::match_single_binding, clippy::match_like_matches_macro)]
                fn has_fd(opcode: OpCode) -> bool {
                    match opcode {
                        #(#event_has_fd_entries)*
                        _ => false,
                    }
                }
             }

            #(#requests)*

            #(#events)*
        }
    }
}

fn generate_request_entry(request: &Request) -> TokenStream {
    let entry = request.enum_entry_ident();
    let request_ident = request.request_ident();
    let entry_doc = format_short_doc(request, |name| format!("The {} request.", name));

    quote! {
        #[doc = #entry_doc]
        #entry(#request_ident)
    }
}

fn generate_request_factory(request: &Request, mod_ident: &Ident) -> TokenStream {
    let param_list = request.args().map(generate_new_param);
    let param_names = request.args().map(|arg| arg.param_ident());
    let request_ident = request.request_ident();
    let factory_name = request.request_factory_ident();
    let factory_doc = format_message_new_doc(&request_ident, false, request.args());

    quote! {
        #[doc = #factory_doc]
        pub fn #factory_name(&self, #(#param_list),*) -> #mod_ident::#request_ident {
            #mod_ident::#request_ident::new(self.id, #(#param_names),*)
        }
    }
}

fn generate_request_from_op_entry((opcode, request): (usize, &Request)) -> TokenStream {
    let request_ident = request.request_ident();
    let opcode: u16 = opcode
        .try_into()
        .expect("too many requests: opcode exceeds u16::MAX");

    quote! {
        #opcode => maker.make::<#request_ident>().map(|m| m.into())?,
    }
}

fn generate_event_entry(event: &Event) -> TokenStream {
    let entry = event.enum_entry_ident();
    let event_ident = event.event_ident();
    let entry_doc = format_short_doc(event, |name| format!("The {} event.", name));

    quote! {
        #[doc = #entry_doc]
        #entry(#event_ident)
    }
}

fn generate_event_factory(event: &Event, mod_ident: &Ident) -> TokenStream {
    let param_list = event.args().map(generate_new_param);
    let param_names = event.args().map(|arg| arg.param_ident());
    let event_ident = event.event_ident();
    let factory_name = event.event_factory_ident();
    let factory_doc = format_message_new_doc(&event_ident, false, event.args());

    quote! {
        #[doc = #factory_doc]
        pub fn #factory_name(&self, #(#param_list),*) -> #mod_ident::#event_ident {
            #mod_ident::#event_ident::new(self.id, #(#param_names),*)
        }
    }
}

fn generate_event_from_op_entry((opcode, event): (usize, &Event)) -> TokenStream {
    let event_ident = event.event_ident();
    let opcode: u16 = opcode
        .try_into()
        .expect("too many requests: opcode exceeds u16::MAX");

    quote! {
        #opcode => maker.make::<#event_ident>().map(|m| m.into())?,
    }
}

fn generate_has_fd_entry((opcode, args): (usize, impl Args)) -> TokenStream {
    let has_fd = args.args().any(|arg| arg.type_name() == "fd");
    let opcode: u16 = opcode
        .try_into()
        .expect("too many requests: opcode exceeds u16::MAX");

    quote! {
        #opcode => #has_fd,
    }
}
