// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A build-time library to generate the `caledon` types to represent
//! [Wayland] protocol XML files.
//!
//! [Wayland]: https://wayland.freedesktop.org/

#![deny(missing_docs, warnings)]

mod error;
mod generator;
mod model;

pub use error::{Error, Result};
pub use generator::{generate, Generator};
