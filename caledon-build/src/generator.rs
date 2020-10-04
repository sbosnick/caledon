// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::path::{Path, PathBuf};

use crate::Result;

/// A builder to configure the process of generating the `caledon` types to represent
/// [Wayland] protocol XML files.
///
/// [Wayland]: https://wayland.freedesktop.org/
#[derive(Debug, PartialEq)]
pub struct Generator {
    directory: Option<PathBuf>,
    out_file: Option<PathBuf>,
    disable_rustfmt: bool,
}

impl Generator {
    /// Create a `Generator` that will generate `caledon` types for all of the
    /// [Wayland] protocol XML files in the `protocol_directory` directory.
    ///
    /// The `Generator` will assume that all XML files in `protocol_directory` are
    /// [Wayland] protocol XML files. `generate` will return an error if any such
    /// XML files cannot be parsed as a [Wayland] protocol XML file.
    ///
    /// [Wayland]: https://wayland.freedesktop.org/
    pub fn new(protocol_directory: impl AsRef<Path>) -> Self {
        Generator {
            directory: Some(protocol_directory.as_ref().to_owned()),
            .. Generator::default()
        }
    }

    /// Set the output file for this `Generator`.
    ///
    /// The default output file if it isn't set with this method is `protocols.rs`
    /// in the directory given by the `OUT_DIR` environment variable. This directory
    /// is appropriate if `Generator` is being run from a `build.rs` file, but
    /// `OUT_DIR` may not be set in other circumstances.
    pub fn out_file(&mut self, file: impl AsRef<Path>) -> &mut Self {
        self.out_file = Some(file.as_ref().to_owned());
        self
    }

    /// Don't run `rustfmt` after generating the `caledon` types.
    ///
    /// The default is to run `rustfmt`.
    pub fn disable_rustfmt(&mut self) -> &mut Self {
        self.disable_rustfmt = true;
        self
    }

    /// Generate the `caledon` types for the configured [Wayland] protocol files.
    ///
    /// The generated types are written to the configured `out_file` or to the
    /// default file if the out file hasn't been set.
    ///
    /// [Wayland]: https://wayland.freedesktop.org/
    pub fn generate(&self) -> Result<()> {
        todo!()
    }
}

/// Create a `Generator` for the `protocols` directory under the directory
/// given by `CARGO_MANIFEST_DIR`.
///
/// This may be useful when the Generator is run from a `build.rs` file
/// but `CARGO_MANIFEST_DIR` may not be set in other circumstances.
impl Default for Generator {
    fn default() -> Self {
        Generator {
            directory: None,
            out_file: None,
            disable_rustfmt: false,
        }
    }
}

/// Convience function to generate the `caledon` types using a default
/// `Generator`.
///
/// This is suitable when it is run from a `build.rs` file may panic
/// if run outside of this context.
pub fn generate() -> Result<()> {
    Generator::default().generate()
}

#[cfg(test)]
mod tests {
    use super::*;

    use assert_matches::assert_matches;

    #[test]
    fn generator_new_sets_directory() {
        let directory = "directory";

        let sut = Generator::new(directory);

        assert_matches!(sut.directory, Some(dir) => {
            assert_eq!(dir, Path::new(directory))
        });
    }

    #[test]
    fn generator_default_sets_expected_values() {
        let expected = Generator {
            directory: None,
            out_file: None,
            disable_rustfmt: false,
        };

        let sut = Generator::default();

        assert_eq!(sut, expected);
    }

    #[test]
    fn generator_out_file_sets_out_file() {
        let filename = "file";

        let mut sut = Generator::default();
        sut.out_file(filename);

        assert_matches!(sut.out_file, Some(file) => {
            assert_eq!(file, Path::new(filename))
        });
    }

    #[test]
    fn generator_disable_rustfmt_does_so() {
        let mut sut = Generator::default();
        sut.disable_rustfmt();

        assert!(sut.disable_rustfmt);
    }
}
