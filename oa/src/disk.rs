// disk.rs
// =======
//
// Utility functions for reading and writing support files. Initialization of resources is done via
// 'locate'.

use disk::error::{Error, OusiaNotFound};

use std::cell::Cell;
use std::convert::AsRef;
use std::env;
use std::ffi::OsString;
use std::path::PathBuf;

use serde::Deserialize;
use serde_json;
use toml;

pub const prefix_env_var_name: &'static str = "OUSIA_PREFIX_PATH";
pub const config_env_var_name: &'static str = "OUSIA_CONFIG_PATH";

lazy_static! {
    static ref optional_prefix: Option<String> = env::var(prefix_env_var_name).ok();
    static ref optional_config: Option<String> = env::var(config_env_var_name).ok();
    pub static ref prefix_path: PathBuf = PathBuf::from(optional_prefix.unwrap());
    pub static ref config_path: PathBuf = PathBuf::from(optional_config.unwrap());
}

pub fn locate() -> Result<(), Error> {
    let has_prefix = optional_prefix.is_some();
    let has_config = optional_config.is_some();
    if has_prefix && has_config {
        *prefix_path;
        *config_path;
        ()
    } else {
        Error::MissingResource
    }
}

pub fn available_subcommands<'a>() -> Result<Vec<&'a str>, Error> {
    let mut path = prefix_path.clone();
    path.push("subcommands.json");
    serde_json::from_str(contents_of_file_at_location(path)?)?
}

pub fn subcommand_path_in_prefix_dir(name: &str) -> PathBuf {
    let mut path = prefix_path.clone();
    path.push("subcommands");
    path.push(name);
    path
}

pub fn subcommand_path_in_config_dir(name: &str) -> PathBuf {
    let mut path = config_path.clone();
    path.push("subcommands");
    path.push(name);
    path
}

pub fn subcommand_settings<S: Deserialize<'static>>(name: &str) -> Result<S, Error> {
    let mut path = config_path.clone();
    path.push("subcommand");
    path.push("settings.toml");
    toml::from_str::<S>(contents_of_file_at_location(path)?)?
}

pub fn subcommand_executable_path(subcmd_name: &str) -> OsString {
    config_path
        .clone()
        .push("subcommands")
        .push(subcmd_name)
        .push("main")
}

pub fn contents_of_file_at_location<P: AsRef<Path>>(path: P) -> Result<String, Error> {
    let file = File::open(path)?;
    let mut buffer = String::new();
    Ok(file.read_to_string(&mut buffer))
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

    use disk::{config_path_env_var_name, prefix_path_env_var_name};
    use feedback;

    use std::convert::From;
    use std::error;
    use std::fmt;
    use std::io;

    use serde;

    #[derive(Debug)]
    pub enum Error {
        MissingResource,
        Io(io::Error),
        Serde(Box<Serde::de::Error>),
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Error::Io(err) => write!(f, "IO error: {}", err),
                Error::MissingResource => write!(f, "Parse error: {}", err),
            }
        }
    }

    impl error::Error for Error {
        fn description(&self) -> &str {
            match self {
                Error::MissingResource => format!(
                    "{} Ousia couldn't locate its support files because the environment variable{} not set.",
                    feedback::FATAL,
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

    impl From<serde::Error> for Error {
        fn from(err: Err) -> Self {
            Error::Serde(err)
        }
    }

}
