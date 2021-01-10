// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use inflector::Inflector;
use itertools::Itertools;
use proc_macro2::Ident;
use std::fmt::Write as _;

use crate::model::{Arg, Documentation};

pub(super) fn format_short_doc<D, F>(doc: D, f: F) -> String
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

// Note: The call to ".intersperse" below is from Itertools but
// there is a an unstable feature to add the same method Iterator.
// Once the Iterator::intersperse method stabalizes this would be
// a name collision, expect that Itertools will likely remove the
// Itertools::intersperse method when this happend. "unstable_name_collisions"
// is a future compatibility lint but in this case the future
// collision is unlikely to occur in practice. This "allow" can
// most likely be removed once Iterator::intersperse has stabalized and
// our MSRV has advanced enough to no longer need the Itertools version.
#[allow(unstable_name_collisions)]
pub(super) fn format_long_doc<D, F>(doc: D, f: F) -> String
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

pub(super) fn format_message_new_doc<'a>(
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
