// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{borrow::Cow, io, path::Path, path::PathBuf};

pub use thiserror::Error;

/// The error type for `caledon-build` operations.
#[derive(Error, Debug)]
pub enum Error {
    /// Error opening a file for parsing.
    #[error("Unable to open file {file}")]
    FileOpen {
        /// The file name that could not be opened.
        file: PathBuf,

        /// The underlying source of the error.
        source: io::Error,
    },

    /// Error attempting to parse a Wayland protocol XML file.
    #[error(transparent)]
    ParseXmlFile(ParseXmlFile),
}

#[derive(Error, Debug)]
#[error("Unable to parse XML file {file}")]
pub struct ParseXmlFile {
    pub file: PathBuf,
    source: serde_xml_rs::Error,
}

impl Error {
    pub(crate) fn file_open(path: Cow<Path>, source: io::Error) -> Error {
        Error::FileOpen {
            file: path.into_owned(),
            source,
        }
    }

    pub(crate) fn parse_xml_file(path: Cow<Path>, source: serde_xml_rs::Error) -> Error {
        Error::ParseXmlFile(ParseXmlFile {
            file: path.into_owned(),
            source,
        })
    }
}

/// A specialized `Result` type for `caledon-build` operations.
pub type Result<T> = std::result::Result<T, Error>;
