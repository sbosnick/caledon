// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::convert::TryInto;

use proc_macro2::{Ident, TokenStream};
use quote::quote;

use crate::model::{Args, Event, Message, Request};

use super::{
    doc::{format_long_doc, format_message_new_doc},
    generate_arg_type, generate_new_param,
};

pub(super) fn generate_request((opcode, request): (usize, &Request)) -> TokenStream {
    let request_ident = request.request_ident();
    let request_doc = format_long_doc(request, |name| format!("The {} request.", name));
    let enum_entry_ident = request.enum_entry_ident();
    let signature = generate_signature(request);
    let new_impl = generate_new_impl(&request_ident, request);
    let opcode: u16 = opcode
        .try_into()
        .expect("too many requests: opcode exceeds u16::MAX");

    quote! {
        #[doc = #request_doc]
        #[derive(Debug, PartialEq)]
        pub struct #request_ident {
            sender: ObjectId,
            args: #signature,
        }

        #new_impl

        impl Message for #request_ident {
            type Signature = #signature;

            type MessageList = Requests;

            const OPCODE: u16 = #opcode;

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

        impl From<#request_ident> for Requests {
            fn from(r: #request_ident) -> Self {
                Self::#enum_entry_ident(r)
            }
        }

        impl TryFrom<Requests> for #request_ident {
            type Error = crate::core::ConversionError;

            fn try_from(i: Requests) -> Result<Self, Self::Error> {
                #[allow(unreachable_patterns)]
                match i {
                    Requests::#enum_entry_ident(inner) => Ok(inner),
                    _ => Err(crate::core::ConversionError::message()),
                }
            }
        }
    }
}

pub(super) fn generate_event((opcode, event): (usize, &Event)) -> TokenStream {
    let event_ident = event.event_ident();
    let event_doc = format_long_doc(event, |name| format!("The {} event.", name));
    let opcode: u16 = opcode
        .try_into()
        .expect("too many events: opcode exceeds u16:MAX");
    let enum_entry_ident = event.enum_entry_ident();
    let signature = generate_signature(event);
    let new_impl = generate_new_impl(&event_ident, event);

    quote! {
        #[doc = #event_doc]
        #[derive(Debug, PartialEq)]
        pub struct #event_ident {
            sender: ObjectId,
            args: #signature,
        }

        #new_impl

        impl Message for #event_ident {
            type Signature = #signature;

            type MessageList = Events;

            const OPCODE: u16 = #opcode;

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

        impl From<#event_ident> for Events {
            fn from(e: #event_ident) -> Self {
                Self::#enum_entry_ident(e)
            }
        }

        impl TryFrom<Events> for #event_ident {
            type Error = crate::core::ConversionError;

            fn try_from(i: Events) -> Result<Self, Self::Error> {
                #[allow(unreachable_patterns)]
                match i {
                    Events::#enum_entry_ident(inner) => Ok(inner),
                    _ => Err(crate::core::ConversionError::message()),
                }
            }
        }
    }
}

fn generate_new_impl(message_ident: &Ident, args: impl Args) -> TokenStream {
    let params = args.args().map(generate_new_param);
    let param_names = args.args().map(|arg| arg.param_ident());
    let new_doc = format_message_new_doc(message_ident, true, args.args());

    quote! {
        impl #message_ident {
            #[doc = #new_doc]
            pub fn new(sender: ObjectId, #(#params),*) -> Self {
                Self {
                    sender,
                    args: (#(#param_names,)*),
                }
            }
        }
    }
}

fn generate_signature(args: impl Args) -> TokenStream {
    let arg_types = args.args().map(generate_arg_type);

    quote! {
        (#(#arg_types,)*)
    }
}
