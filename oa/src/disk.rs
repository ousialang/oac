// disk.rs
// =======
//
// Utility functions for reading and writing support files. Initialization of resources is done via
// 'locate'.

use disk::error::Error;
use serde::Deserialize;
use serde_json;
use std::cell::Cell;
use std::convert::AsRef;
use std::env;
use std::ffi::OsString;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use toml;

pub const PREFIX_PATH_ENV_VAR_NAME: &'static str = "OUSIA_PREFIX_PATH";
pub const CONFIG_PATH_ENV_VAR_NAME: &'static str = "OUSIA_CONFIG_PATH";

lazy_static! {
    static ref OPTIONAL_PREFIX_PATH: Result<PathBuf, env::VarError> =
        { env::var(PREFIX_PATH_ENV_VAR_NAME).map(|s| PathBuf::from(s)) };
    static ref OPTIONAL_CONFIG_PATH: Result<PathBuf, env::VarError> =
        { env::var(CONFIG_PATH_ENV_VAR_NAME).map(|s| PathBuf::from(s)) };
    pub static ref PREFIX_PATH: PathBuf = OPTIONAL_PREFIX_PATH.unwrap();
    pub static ref CONFIG_PATH: PathBuf = OPTIONAL_CONFIG_PATH.unwrap();
}

pub fn locate() -> Result<(), Error> {
    let has_prefix = (*OPTIONAL_PREFIX_PATH).is_ok();
    let has_config = (*OPTIONAL_CONFIG_PATH).is_ok();
    if has_prefix && has_config {
        *PREFIX_PATH;
        *CONFIG_PATH;
        Ok(())
    } else {
        Err(Error::MissingResource)
    }
}

pub fn available_subcommands<'a>() -> Result<Vec<&'a str>, Error> {
    let mut path = PREFIX_PATH.clone();
    path.push("subcommands.json");
    serde_json::from_str(contents_of_file_at_location(path)?)?
}

pub fn subcommand_path_in_prefix_dir(name: &str) -> PathBuf {
    let mut path = PREFIX_PATH.clone();
    path.push("subcommands");
    path.push(name);
    path
}

pub fn subcommand_path_in_config_dir(name: &str) -> PathBuf {
    let mut path = CONFIG_PATH.clone();
    path.push("subcommands");
    path.push(name);
    path
}

pub fn subcommand_settings<S: Deserialize<'static>>(name: &str) -> Result<S, Error> {
    let mut path = CONFIG_PATH.clone();
    path.push("subcommand");
    path.push("settings.toml");
    Ok(toml::from_str::<S>(&*(contents_of_file_at_location(path)?)).unwrap())
}

pub fn subcommand_executable_path(subcmd_name: &str) -> OsString {
    let path = CONFIG_PATH.clone();
    path.push("subcommands");
    path.push(subcmd_name);
    path.push("main");
    path.into_os_string()
}

pub fn contents_of_file_at_location<P: AsRef<Path>>(path: P) -> Result<String, Error> {
    let file = File::open(path)?;
    let mut buffer = String::new();
    file.read_to_string(&mut buffer)?;
    Ok(buffer)
}

pub mod schemas {

    #[derive(Serialize, Deserialize)]
    pub struct Subcommand {
        kind: SubcommandKind,
        alias: Option<Vec<String>>,
    }

    #[derive(Serialize, Deserialize)]
    pub enum SubcommandKind {
        Internal,
        External,
    }
}

pub mod error {
    use colored::*;
    use feedback;
    use serde;
    use std::convert::From;
    use std::error;
    use std::fmt;
    use std::io;

    #[derive(Debug)]
    pub enum Error {
        MissingResource,
        Io(io::Error),
        //Serde(Box<serde::de::Error>),
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Error::Io(err) => write!(f, "IO error: {}", err),
                Error::MissingResource => write!(f, "Missing resources"),
            }
        }
    }

    impl error::Error for Error {
        fn description(&self) -> &str {
            match self {
                Error::MissingResource => format!(
                    "{} Ousia couldn't locate its support files because the environment variable{} not set.",
                    *feedback::FATAL,
                    "foobar"
                ),
                Error::Io(err) => err.description(),
            }
        }
    }

    impl From<io::Error> for Error {
        fn from(err: io::Error) -> Self {
            Error::Io(err)
        }
    }
    /*
    impl From<T> for Error where T: serde::de::Error {
        fn from(err: T) -> Self {
            Error::Serde(Box::new(err))
        }
    }
*/
}
