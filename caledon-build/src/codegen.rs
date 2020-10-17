// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{convert::TryInto, fmt::Write as _, io::Write};

use inflector::Inflector;
use itertools::Itertools;
use proc_macro2::{Ident, TokenStream};
use quote::quote;

use crate::{
    model::{Arg, Args, Documentation, Event, Interface, Protocol, Request},
    Error, Result,
};

pub fn generate_code<'a, W, I>(mut file: W, protocols: I) -> Result<()>
where
    W: Write,
    I: Iterator<Item = &'a Protocol> + Clone,
{
    writeln!(
        file,
        "// File generated by caledon-build from the following input files:"
    )
    .map_err(Error::file_write)?;
    for protocol in protocols.clone() {
        writeln!(file, "//     {}", protocol.path().display()).map_err(Error::file_write)?;
    }

    let entries = protocols.clone().map(generate_protocol_list_entry);
    let modules = protocols.map(generate_protocol);

    let output = quote! {
        use crate::core::ProtocolFamily;

        #[doc = "The list of protocols implemented by caledon."]
        pub enum Protocols {
            #(#entries,)*
        }

        impl ProtocolFamily for Protocols { }

        #(#modules)*
    };

    write!(file, "{}", output).map_err(Error::file_write)
}

fn generate_protocol(protocol: &Protocol) -> TokenStream {
    let mod_ident = protocol.mod_ident();
    let protocol_ident = protocol.protocol_ident();
    let interfaces_ident = protocol.interfaces_ident();
    let enum_entry_ident = protocol.enum_entry_ident();
    let mod_doc = format_long_doc(protocol, |name| {
        format!("Caledon types for the {} protocol.", name)
    });
    let protocol_doc = format!("The {} protocol.", protocol.name());
    let interfaces_doc = format!("The interfaces of the {} protocol.", protocol.name());
    let entries = protocol.interfaces().map(generate_interface_entry);
    let interfaces = protocol
        .interfaces()
        .map(|i| generate_interface(i, &interfaces_ident));

    quote! {
        #[allow(clippy::too_many_arguments)]
        #[doc = #mod_doc]
        pub mod #mod_ident {
            use std::convert::TryFrom;

            #[allow(unused_imports)]
            use std::ffi::CString;

            use crate::core::{Interface, InterfaceList, ObjectId, Protocol};

            #[allow(unused_imports)]
            use crate::core::{Decimal, Fd};

            #[doc = #protocol_doc]
            pub struct #protocol_ident;

            impl Protocol for #protocol_ident {
                type Interfaces = #interfaces_ident;

                type ProtocolList = super::Protocols;
            }

            impl From<#protocol_ident> for super::Protocols {
                fn from(t: #protocol_ident) -> Self {
                    Self::#enum_entry_ident(t)
                }
            }

            impl TryFrom<super::Protocols> for #protocol_ident {
                type Error = crate::core::ConversionError;

                fn try_from(p: super::Protocols) -> Result<Self, Self::Error> {
                    #[allow(unreachable_patterns)]
                    match p {
                        super::Protocols::#enum_entry_ident(inner) => Ok(inner),
                        _ => Err(crate::core::ConversionError::protocol()),
                    }
                }
            }

            #[doc = #interfaces_doc]
            pub enum #interfaces_ident {
                #(#entries,)*
            }

            impl InterfaceList for #interfaces_ident {
                type Protocol = #protocol_ident;
            }

            #(#interfaces)*
        }
    }
}

fn generate_protocol_list_entry(protocol: &Protocol) -> TokenStream {
    let entry = protocol.enum_entry_ident();
    let mod_ident = protocol.mod_ident();
    let protocol_ident = protocol.protocol_ident();
    let entry_doc = format_short_doc(protocol, |name| format!("The {} protocol.", name));

    quote! {
        #[doc = #entry_doc]
        #entry(#mod_ident::#protocol_ident)
    }
}

fn generate_interface(interface: &Interface, interface_list: &Ident) -> TokenStream {
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
    let event_entries = interface.events().map(generate_event_entry);
    let events = interface.events().enumerate().map(generate_event);
    let event_factories = interface
        .events()
        .map(|e| generate_event_factory(e, &mod_ident));

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
            type InterfaceList = #interface_list;
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

            use crate::core::{Message, MessageList, ObjectId};

            #[allow(unused_imports)]
            use crate::core::{Decimal, Fd};

            #[doc = #req_doc]
            pub enum Requests {
                #(#request_entries,)*
            }

            impl MessageList for Requests {
                type Interface = super::#interface_ident;
            }

            #[doc = #evt_doc]
            pub enum Events {
                #(#event_entries,)*
            }

            impl MessageList for Events {
                type Interface = super::#interface_ident;
            }

            #(#requests)*

            #(#events)*
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

fn generate_request((opcode, request): (usize, &Request)) -> TokenStream {
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

fn generate_event((opcode, event): (usize, &Event)) -> TokenStream {
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

fn generate_new_param(arg: &Arg) -> TokenStream {
    let arg_type = generate_arg_type(arg);
    let param_name = arg.param_ident();

    quote! {
        #param_name: #arg_type
    }
}

fn generate_signature(args: impl Args) -> TokenStream {
    let arg_types = args.args().map(generate_arg_type);

    quote! {
        (#(#arg_types,)*)
    }
}

fn generate_arg_type(arg: &Arg) -> TokenStream {
    match arg.type_name() {
        "new_id" | "object" => quote! { ObjectId },
        "int" => quote! { i32 },
        "uint" => quote! { u32 },
        "fixed" => quote! { Decimal },
        "string" => quote! { CString },
        "array" => quote! { Box<[u8]> },
        "fd" => quote! { Fd },
        _ => panic!(
            "Encountered an unexpected argument type: {}",
            arg.type_name()
        ),
    }
}

fn format_short_doc<D, F>(doc: D, f: F) -> String
where
    D: Documentation,
    F: Fn(&str) -> String,
{
    doc.description().map_or_else(
        || f(doc.name()),
        |desc| {
            let mut s = desc.summary().to_sentence_case();
            if !s.ends_with('.') {
                s.push('.');
            }
            s
        },
    )
}

fn format_long_doc<D, F>(doc: D, f: F) -> String
where
    D: Documentation,
    F: Fn(&str) -> String,
{
    doc.description().map_or_else(
        || f(doc.name()),
        |desc| {
            let mut s = desc.summary().to_sentence_case();
            if !s.ends_with('.') {
                s.push('.');
            }
            if let Some(detail) = desc.detail() {
                s += "\n\n";
                s.extend(detail.lines().map(|l| l.trim_start()).intersperse("\n"));
            }
            s
        },
    )
}

fn format_message_new_doc<'a>(
    message_ident: &Ident,
    incl_sender: bool,
    args: impl Iterator<Item = &'a Arg>,
) -> String {
    let mut args = args.peekable();
    let mut s = format!("Create a new `{}`.", message_ident);

    if incl_sender || args.peek().is_some() {
        s += "\n\n# Parameters\n\n| Name | Description |\n|---|---|\n";
    }

    if incl_sender {
        s += "| `sender` | the object sending the message |\n";
    }

    for arg in args {
        writeln!(
            s,
            "| `{}` | {} {} |",
            arg.param_name(),
            arg.summary().unwrap_or(""),
            if arg.type_name() == "new_id" {
                "(a new_id)"
            } else {
                ""
            }
        )
        .expect("Write to string failed");
    }

    s
}
