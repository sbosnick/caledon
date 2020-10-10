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

    /// Error creating a file for output.
    #[error("Unable to create file {file}")]
    FileCreate {
        /// The file name the could not be created.
        file: PathBuf,

        /// The underlying source of the error.
        source: io::Error,
    },

    /// Error when writing to the output file.
    #[error("Unable to write to the output file.")]
    FileWrite {
        /// The underlying source of the error.
        source: io::Error,
    },

    /// Error reading a directory.
    #[error("Unable to read the directory {dir}")]
    ReadDir {
        /// The directory that could not be read.
        dir: PathBuf,

        /// The underlying source of the error.
        source: io::Error,
    },

    /// Error reading a directory entry.
    #[error("Unable to read an entry of a directory")]
    ReadDirEntry {
        /// The underlying source of the error.
        source: io::Error,
    },

    /// Error attempting to parse a Wayland protocol XML file.
    #[error(transparent)]
    ParseXmlFile(ParseXmlFile),

    /// Error retrieving an expected environment variable.
    ///
    /// This is usually related to not running as a part of a `build.rs`
    /// file.
    #[error("Expected environment variable {0} not set")]
    NoEnvVar(String),

    /// Error when attempting to spawn rustfmt.
    #[error("Unable to spawn rustfmt for file {file}")]
    SpawnRustFmt {
        /// The file on which we were trying to run rustfmt.
        file: PathBuf,

        /// The underlying source of the error.
        source: io::Error,
    },

    /// Error when rustfmt did not exit successfully.
    #[error("rustfmt exited unsucessfuly for file {file}")]
    RunRustFmt {
        /// The file on wich we were trying to run rustfmt.
        file: PathBuf,
    },
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

    pub(crate) fn file_create(path: Cow<Path>, source: io::Error) -> Error {
        Error::FileCreate {
            file: path.into_owned(),
            source,
        }
    }

    pub(crate) fn file_write(source: io::Error) -> Error {
        Error::FileWrite { source }
    }

    pub(crate) fn read_dir(path: Cow<Path>, source: io::Error) -> Error {
        Error::ReadDir {
            dir: path.into_owned(),
            source,
        }
    }

    pub(crate) fn read_dir_entry(source: io::Error) -> Error {
        Error::ReadDirEntry { source }
    }

    pub(crate) fn spawn_rustfmt(path: Cow<Path>, source: io::Error) -> Error {
        Error::SpawnRustFmt {
            file: path.into_owned(),
            source,
        }
    }

    pub(crate) fn run_rustfmt(path: Cow<Path>) -> Error {
        Error::RunRustFmt {
            file: path.into_owned(),
        }
    }
}

/// A specialized `Result` type for `caledon-build` operations.
pub type Result<T> = std::result::Result<T, Error>;
