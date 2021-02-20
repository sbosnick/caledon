// Copyright 2020 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{
    env,
    ffi::OsStr,
    ffi::OsString,
    fs,
    fs::File,
    io,
    io::BufWriter,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

use itertools::Itertools;

use crate::{codegen::generate_code, model::Protocol, Error, Result};

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
            ..Generator::default()
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
        let file = self.get_out_file()?;
        let protocols: Vec<_> = self
            .get_directory()?
            .filter_map(dir_entry_to_protocol)
            .try_collect()?;

        generate_code(file, protocols.iter())?;

        for protocol in protocols.iter() {
            println!("cargo:rerun-if-changed={}", protocol.path().display());
        }

        let path = self.get_directory_path()?;
        println!("cargo:rerun-if-changed={}", path.display());

        self.run_rustfmt()
    }

    fn get_directory(&self) -> Result<fs::ReadDir> {
        // false positive: env::var_os has too general a type to be passed directly
        #[allow(clippy::redundant_closure)]
        get_directory(&self.directory, |k| env::var_os(k))
    }

    fn get_directory_path(&self) -> Result<PathBuf> {
        // false positive: env::var_os has too general a type to be passed directly
        #[allow(clippy::redundant_closure)]
        get_directory_path(&self.directory, |k| env::var_os(k))
    }

    fn get_out_file(&self) -> Result<impl Write> {
        // false positive: env::var_os has too general a type to be passed directly
        #[allow(clippy::redundant_closure)]
        get_out_file(&self.out_file, |k| env::var_os(k))
    }

    fn run_rustfmt(&self) -> Result<()> {
        if !self.disable_rustfmt {
            // false positive: env::var_os has too general a type to be passed directly
            #[allow(clippy::redundant_closure)]
            run_rustfmt(&self.out_file, |k| env::var_os(k))?;
        }
        Ok(())
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

fn dir_entry_to_protocol(entry: io::Result<fs::DirEntry>) -> Option<Result<Protocol>> {
    match entry {
        Ok(entry) if is_xml_file(&entry) => Some(Protocol::new(entry.path())),
        Ok(_) => None,
        Err(e) => Some(Err(Error::read_dir_entry(e))),
    }
}

fn is_xml_file(entry: &fs::DirEntry) -> bool {
    match (entry.file_type(), entry.path().extension()) {
        (Ok(ft), Some(ext)) => ft.is_file() && is_xml_ext(ext),
        (_, _) => false,
    }
}

fn is_xml_ext(ext: &OsStr) -> bool {
    ext.to_str()
        .map_or(false, |ext| "xml".eq_ignore_ascii_case(ext))
}

fn get_out_file<G>(path: &Option<PathBuf>, var_os: G) -> Result<impl Write>
where
    G: Fn(&OsStr) -> Option<OsString>,
{
    convert_or_default(path, "OUT_DIR", "protocols.rs", create_file, var_os).map(BufWriter::new)
}

fn create_file(path: &Path) -> Result<File> {
    File::create(path).map_err(|e| Error::file_create(path.into(), e))
}

fn run_rustfmt<G>(path: &Option<PathBuf>, var_os: G) -> Result<()>
where
    G: Fn(&OsStr) -> Option<OsString>,
{
    let path = convert_or_default(path, "OUT_DIR", "protocols.rs", to_pathbuf, var_os)?;

    Command::new("rustfmt")
        .arg(&path)
        .status()
        .map_err(|source| Error::spawn_rustfmt((&path).into(), source))
        .and_then(|status| {
            if status.success() {
                Ok(())
            } else {
                Err(Error::run_rustfmt(path.into()))
            }
        })
}

// NOTE: to_pathbuf is passed to convert_or_default in a postion that expects a Result return
// value. Some of the other functions passed in that postion can return an Err variant so we have
// to allow the unnessary wraps here.
#[allow(clippy::unnessary_wraps)]
fn to_pathbuf(path: &Path) -> Result<PathBuf> {
    Ok(path.to_path_buf())
}

fn get_directory<G>(path: &Option<PathBuf>, var_os: G) -> Result<fs::ReadDir>
where
    G: Fn(&OsStr) -> Option<OsString>,
{
    convert_or_default(path, "CARGO_MANIFEST_DIR", "protocols", read_dir, var_os)
}

fn get_directory_path<G>(path: &Option<PathBuf>, var_os: G) -> Result<PathBuf>
where
    G: Fn(&OsStr) -> Option<OsString>,
{
    convert_or_default(path, "CARGO_MANIFEST_DIR", "protocols", to_pathbuf, var_os)
}

fn read_dir(path: &Path) -> Result<fs::ReadDir> {
    fs::read_dir(path).map_err(|e| Error::read_dir(path.into(), e))
}

fn convert_or_default<K, P, F, R, G>(
    path: &Option<PathBuf>,
    key: K,
    suffix: P,
    f: F,
    var_os: G,
) -> Result<R>
where
    K: AsRef<OsStr>,
    P: AsRef<Path>,
    F: Fn(&Path) -> Result<R>,
    G: Fn(&OsStr) -> Option<OsString>,
{
    let key = key.as_ref();

    path.as_ref().map_or_else(
        || {
            var_os(key).map_or_else(
                || Err(Error::NoEnvVar(key.to_string_lossy().into_owned())),
                |s| f(&Path::new(&s).join(suffix)),
            )
        },
        |p| f(&p),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{cell::RefCell, sync::Arc};

    use assert_matches::assert_matches;
    use tempfile::tempdir;

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

    #[test]
    fn generator_get_out_file_get_configured_file() {
        let dir = tempdir().expect("Can't get temporary directory.");
        let path = dir.path().join("myfile.txt");
        let text = "Hi there!";

        let mut sut = Generator::default();
        sut.out_file(&path);
        let mut file = sut.get_out_file().expect("Can't get out file.");
        write!(file, "{}", text).expect("Can't write to out file.");
        drop(file);

        let contents = fs::read_to_string(path).expect("Can't read contents.");
        assert_eq!(contents, text);
    }

    #[test]
    fn get_out_file_gets_from_out_dir() {
        let dir = tempdir().expect("Can't get temporary directory.");
        let state: Arc<RefCell<Option<OsString>>> = Default::default();
        let state_clone = state.clone();
        let var_os = |k: &OsStr| {
            *state_clone.borrow_mut() = Some(k.to_os_string());
            Some(dir.path().as_os_str().to_os_string())
        };
        let text = "Hi there!";

        let mut file = get_out_file(&None, var_os).expect("Can't get out file.");
        write!(file, "{}", text).expect("Can't write to out file.");
        drop(file);

        let contents =
            fs::read_to_string(dir.path().join("protocols.rs")).expect("Can't read contents.");
        assert_eq!(contents, text);
        assert_eq!(*state.borrow(), Some(OsString::from("OUT_DIR")));
    }

    #[test]
    fn get_out_file_without_out_dir_or_configure_is_err() {
        let var_os = |_: &OsStr| None;

        let result = get_out_file(&None, var_os);

        assert!(result.is_err());
    }

    #[test]
    fn get_directory_gets_configured_directory() {
        let dir = tempdir().expect("Can't get temporary directory.");
        fs::write(dir.path().join("myfile.txt"), "Hi there!")
            .expect("Can't write to to temporary file.");

        let dirs: Vec<_> = get_directory(&Some(dir.path().into()), |_| panic!("Got env var."))
            .expect("Can't get directory")
            .try_collect()
            .expect("Can't get entries.");

        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0].file_name(), "myfile.txt");
    }

    #[test]
    fn get_directory_gets_from_expected_env_var_without_config() {
        let _ = get_directory(&None, |k| {
            assert_eq!(k, OsStr::new("CARGO_MANIFEST_DIR"));
            None
        });
    }

    #[test]
    fn get_directory_gets_from_env_var_without_config() {
        let dir = tempdir().expect("Can't get temporary directory.");
        let path = dir.path().join("protocols");
        fs::create_dir(&path).expect("Can't create directory.");
        fs::write(path.join("myfile.txt"), "Hi there!").expect("Can't write to to temporary file.");

        let dirs: Vec<_> = get_directory(&None, |_| Some(dir.path().as_os_str().to_os_string()))
            .expect("Can't get directory")
            .try_collect()
            .expect("Can't get entries.");

        assert_eq!(dirs.len(), 1);
        assert_eq!(dirs[0].file_name(), "myfile.txt");
    }

    #[test]
    fn get_directory_without_config_or_env_var_is_error() {
        let result = get_directory(&None, |_| None);

        assert!(result.is_err());
    }

    #[test]
    fn to_protocol_is_none_for_non_xml_file() {
        let dir = tempdir().expect("Can't get temporary directory.");
        fs::write(dir.path().join("myfile.txt"), "Hi there!")
            .expect("Can't write to temporary file.");
        let mut entries = fs::read_dir(dir.path()).expect("Can't read dir");

        let entry = entries.next().expect("Can't get next entry.");
        let result = dir_entry_to_protocol(entry);

        assert!(result.is_none());
    }

    #[test]
    fn to_protocol_is_protocol_for_xml_file() {
        let dir = tempdir().expect("Can't get temporary directory.");
        fs::copy(get_test_file("tests.xml"), dir.path().join("tests.xml"))
            .expect("Can't copy tests.xml file.");
        let mut entries = fs::read_dir(dir.path()).expect("Can't read dir");

        let entry = entries.next().expect("Can't get next entry.");
        let result = dir_entry_to_protocol(entry);

        assert_matches!(result, Some(Ok(_)));
    }

    #[test]
    fn to_protocol_is_none_for_xml_directory() {
        let dir = tempdir().expect("Can't get temporary directory.");
        fs::create_dir(dir.path().join("tests.xm")).expect("Can't create directory.");
        let mut entries = fs::read_dir(dir.path()).expect("Can't read dir");

        let entry = entries.next().expect("Can't get next entry.");
        let result = dir_entry_to_protocol(entry);

        assert!(result.is_none());
    }

    fn get_test_file(test_file: &str) -> PathBuf {
        let mut path = PathBuf::from("test_data");
        path.push(test_file);

        path
    }
}
