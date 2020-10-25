// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{fs::File, io::BufReader, path::Path, path::PathBuf, slice};

use inflector::Inflector;
use proc_macro2::Ident;
use quote::format_ident;
use serde::Deserialize;
use serde_xml_rs::from_reader;

use crate::{Error, Result};

// The DTD fragments in the comments of this file are (when taken all together)
// the "wayland.dtd" file from the protocol directory of the Wayland repository
// (at least as of September 2020). The struct's and enum's that follow the DTD fragment
// are a loose attempt to parse that portion of a Wayland protocol file through the
// serde Deserialize derivations and the serde_xml_rs crate. The goal is to recognize
// all valid (according to the DTD) protocol files, but not necessiarily to reject all
// invalid ones.

// <!ELEMENT protocol (copyright?, description?, interface+)>
//   <!ATTLIST protocol name CDATA #REQUIRED>
#[derive(Debug, Deserialize)]
pub struct Protocol {
    #[serde(skip)]
    path: PathBuf,

    name: String,
    copyright: Option<Copyright>,
    description: Option<Description>,
    #[serde(rename = "interface")]
    interfaces: Vec<Interface>,
}

// <!ELEMENT copyright (#PCDATA)>
#[derive(Debug, Deserialize)]
pub struct Copyright {
    #[serde(rename = "$value")]
    body: String,
}

// <!ELEMENT interface (description?,(request|event|enum)+)>
//   <!ATTLIST interface name CDATA #REQUIRED>
//   <!ATTLIST interface version CDATA #REQUIRED>
#[derive(Debug, Deserialize)]
pub struct Interface {
    name: String,
    version: String,
    #[serde(rename = "$value")]
    items: Vec<InterfaceItem>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum InterfaceItem {
    // Note: The description item doesn't really belong here but is included
    // to make the derive(Deserialize) work with serde_xml_rs. This allows having
    // more then 1 description or having a description but no request, event, or enum
    // items, neither of which is allowed by the DTD. This shouldn't be a problem
    // in practice as this is over-inclusive and will still recognize all valid
    // protocol XML files.
    Description(Description),
    Request(Request),
    Event(Event),
    Enum(Enum),
}

// <!ELEMENT request (description?,arg*)>
//   <!ATTLIST request name CDATA #REQUIRED>
//   <!ATTLIST request type CDATA #IMPLIED>
//   <!ATTLIST request since CDATA #IMPLIED>
#[derive(Debug, Deserialize)]
pub struct Request {
    name: String,
    #[serde(rename = "type")]
    type_name: Option<String>,
    since: Option<String>,
    description: Option<Description>,
    #[serde(rename = "arg")]
    args: Option<Vec<Arg>>,
}

// <!ELEMENT event (description?,arg*)>
//   <!ATTLIST event name CDATA #REQUIRED>
//   <!ATTLIST event since CDATA #IMPLIED>
#[derive(Debug, Deserialize)]
pub struct Event {
    name: String,
    since: Option<String>,
    description: Option<Description>,
    #[serde(rename = "arg")]
    args: Option<Vec<Arg>>,
}

// <!ELEMENT enum (description?,entry*)>
//   <!ATTLIST enum name CDATA #REQUIRED>
//   <!ATTLIST enum since CDATA #IMPLIED>
//   <!ATTLIST enum bitfield CDATA #IMPLIED>
#[derive(Debug, Deserialize)]
pub struct Enum {
    name: String,
    since: Option<String>,
    bitfield: Option<String>,
    description: Option<Description>,
    #[serde(rename = "entry")]
    entries: Option<Vec<Entry>>,
}

// <!ELEMENT entry (description?)>
//   <!ATTLIST entry name CDATA #REQUIRED>
//   <!ATTLIST entry value CDATA #REQUIRED>
//   <!ATTLIST entry summary CDATA #IMPLIED>
//   <!ATTLIST entry since CDATA #IMPLIED>
#[derive(Debug, Deserialize)]
pub struct Entry {
    name: String,
    value: String,
    summary: Option<String>,
    since: Option<String>,
    description: Option<Description>,
}

// <!ELEMENT arg (description?)>
//   <!ATTLIST arg name CDATA #REQUIRED>
//   <!ATTLIST arg type CDATA #REQUIRED>
//   <!ATTLIST arg summary CDATA #IMPLIED>
//   <!ATTLIST arg interface CDATA #IMPLIED>
//   <!ATTLIST arg allow-null CDATA #IMPLIED>
//   <!ATTLIST arg enum CDATA #IMPLIED>
#[derive(Debug, Deserialize)]
pub struct Arg {
    name: String,
    #[serde(rename = "type")]
    type_name: String,
    summary: Option<String>,
    interface: Option<String>,
    allow_null: Option<String>,
    #[serde(rename = "enum")]
    enum_name: Option<String>,
    description: Option<Description>,
}

// <!ELEMENT description (#PCDATA)>
//   <!ATTLIST description summary CDATA #REQUIRED>
#[derive(Debug, Deserialize)]
pub struct Description {
    summary: String,

    // the DTD suggest this is required but it is not always present
    #[serde(rename = "$value")]
    body: Option<String>,
}

// === impl ===
pub trait Documentation {
    fn name(&self) -> &str;
    fn description(&self) -> Option<&Description>;
}

pub trait Args {
    fn args(&self) -> ArgIter;
}

impl Protocol {
    pub fn new(path: impl AsRef<Path>) -> Result<Protocol> {
        let path = path.as_ref();
        let file = File::open(path).map_err(|e| Error::file_open(path.into(), e))?;
        from_reader(BufReader::new(file))
            .map(|mut p: Protocol| {
                p.path = path.to_path_buf();
                p
            })
            .map_err(|e| Error::parse_xml_file(path.into(), e))
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn mod_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_snake_case())
    }

    pub fn protocol_ident(&self) -> Ident {
        format_ident!("{}Protocol", self.name.to_class_case())
    }

    pub fn protocol_requests_ident(&self) -> Ident {
        format_ident!("{}ProtocolRequests", self.name.to_class_case())
    }

    pub fn protocol_events_ident(&self) -> Ident {
        format_ident!("{}ProtocolEvents", self.name.to_class_case())
    }

    pub fn enum_entry_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_class_case())
    }

    pub fn interfaces(&self) -> impl Iterator<Item = &Interface> + Clone {
        self.interfaces.iter()
    }
}

impl Documentation for &Protocol {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> Option<&Description> {
        self.description.as_ref()
    }
}

impl Interface {
    pub fn mod_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_snake_case())
    }
    pub fn interface_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_class_case())
    }

    pub fn enum_entry_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_class_case())
    }

    pub fn requests(&self) -> impl Iterator<Item = &Request> {
        self.items.iter().filter_map(|item| match item {
            InterfaceItem::Request(req) => Some(req),
            _ => None,
        })
    }

    pub fn events(&self) -> impl Iterator<Item = &Event> {
        self.items.iter().filter_map(|item| match item {
            InterfaceItem::Event(evt) => Some(evt),
            _ => None,
        })
    }
}

impl Documentation for &Interface {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> Option<&Description> {
        self.items.iter().find_map(|item| match item {
            InterfaceItem::Description(desc) => Some(desc),
            _ => None,
        })
    }
}

impl Request {
    pub fn enum_entry_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_class_case())
    }

    pub fn request_ident(&self) -> Ident {
        format_ident!("{}Request", self.name.to_class_case())
    }

    pub fn request_factory_ident(&self) -> Ident {
        format_ident!("{}_request", self.name.to_snake_case())
    }
}

impl Documentation for &Request {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> Option<&Description> {
        self.description.as_ref()
    }
}

impl Args for &Request {
    fn args(&self) -> ArgIter {
        ArgIter::new(&self.args)
    }
}

impl Event {
    pub fn enum_entry_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_class_case())
    }

    pub fn event_ident(&self) -> Ident {
        format_ident!("{}Event", self.name.to_class_case())
    }

    pub fn event_factory_ident(&self) -> Ident {
        format_ident!("{}_event", self.name.to_snake_case())
    }
}

impl Documentation for &Event {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> Option<&Description> {
        self.description.as_ref()
    }
}

impl Args for &Event {
    fn args(&self) -> ArgIter {
        ArgIter::new(&self.args)
    }
}

impl Arg {
    pub fn type_name(&self) -> &str {
        &self.type_name
    }

    pub fn param_ident(&self) -> Ident {
        format_ident!("{}", self.name.to_snake_case())
    }

    pub fn param_name(&self) -> String {
        self.name.to_snake_case()
    }

    pub fn summary(&self) -> Option<&str> {
        self.summary.as_deref()
    }
}

impl Description {
    pub fn summary(&self) -> &str {
        &self.summary
    }

    pub fn detail(&self) -> Option<&str> {
        self.body.as_deref()
    }
}

pub struct ArgIter<'a> {
    inner: Option<slice::Iter<'a, Arg>>,
}

impl<'a> ArgIter<'a> {
    fn new(args: &'a Option<Vec<Arg>>) -> Self {
        Self {
            inner: args.as_deref().map(|s| s.iter()),
        }
    }
}

impl<'a> Iterator for ArgIter<'a> {
    type Item = &'a Arg;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.as_mut() {
            Some(i) => i.next(),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    use serde_xml_rs::from_str;

    #[test]
    fn protocol_parses_from_test_xml() {
        simple_logger::SimpleLogger::new().init().unwrap();

        from_str::<Protocol>(TEST_XML_PROTOCOL).expect("Unable to parse test xml.");
    }

    #[test]
    fn protocol_has_expected_name() {
        let protocol = from_str::<Protocol>(TEST_XML_PROTOCOL).unwrap();

        assert_eq!(protocol.name, "build_time_wayland_tests");
    }

    #[test]
    fn protocol_has_copyright_no_description() {
        let protocol = from_str::<Protocol>(TEST_XML_PROTOCOL).unwrap();

        assert!(protocol.copyright.is_some());
        assert!(protocol.description.is_none());
    }

    #[test]
    fn protocol_has_one_interface() {
        let protocol = from_str::<Protocol>(TEST_XML_PROTOCOL).unwrap();

        assert_eq!(protocol.interfaces.len(), 1);
    }

    #[test]
    fn interface_has_description() {
        let protocol = from_str::<Protocol>(TEST_XML_PROTOCOL).unwrap();
        let items = &protocol.interfaces[0].items;

        let description = items.iter().find(|item| {
            if let InterfaceItem::Description(_) = item {
                true
            } else {
                false
            }
        });

        assert!(description.is_some());
    }

    #[test]
    fn event_fd_has_fd_arg() {
        let protocol = from_str::<Protocol>(TEST_XML_PROTOCOL).unwrap();
        let items = &protocol.interfaces[0].items;
        let event = items
            .iter()
            .filter_map(|item| match item {
                InterfaceItem::Event(event) if event.name == "fd" => Some(event),
                _ => None,
            })
            .nth(0)
            .expect("Can't find event \"fd\"");

        let arg = &event.args.as_ref().unwrap()[0];

        assert_eq!(arg.name, "fd");
    }

    #[test]
    fn protocol_new_parses_xml_file() {
        let path = get_test_file("tests.xml");

        Protocol::new(path).expect("Unable to parse test.xml file.");
    }

    fn get_test_file(test_file: &str) -> PathBuf {
        let mut path = PathBuf::from("test_data");
        path.push(test_file);

        path
    }

    // This is the tests.xml file from the Wayland repository protocol directory.
    static TEST_XML_PROTOCOL: &'static str = r##"
        <?xml version="1.0" encoding="UTF-8"?>
        <protocol name="build_time_wayland_tests">

          <copyright>
            Copyright © 2017 Samsung Electronics Co., Ltd

            Permission is hereby granted, free of charge, to any person
            obtaining a copy of this software and associated documentation files
            (the "Software"), to deal in the Software without restriction,
            including without limitation the rights to use, copy, modify, merge,
            publish, distribute, sublicense, and/or sell copies of the Software,
            and to permit persons to whom the Software is furnished to do so,
            subject to the following conditions:

            The above copyright notice and this permission notice (including the
            next paragraph) shall be included in all copies or substantial
            portions of the Software.

            THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
            EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
            MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
            NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
            BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
            ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
            CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
            SOFTWARE.
          </copyright>

          <interface name="fd_passer" version="2">
            <description summary="Sends an event with an fd">
              A trivial interface for fd passing tests.
            </description>

            <request name="destroy" type="destructor"/>

            <event name="pre_fd"/>

            <event name="fd">
              <description summary="passes a file descriptor"/>
              <arg name="fd" type="fd" summary="file descriptor"/>
            </event>

            <!-- Version 2 additions -->
            <request name="conjoin" since="2">
              <description summary="register another fd passer with this one">
                Tells this fd passer object about another one to send events
                to for more complicated fd leak tests.
              </description>
              <arg name="passer" type="object" interface="fd_passer"/>
            </request>
          </interface>
        </protocol>
"##;
}
