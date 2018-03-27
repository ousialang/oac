use std::env::var_os;
use std::path::PathBuf;


pub const VERSION_MAJOR: &'static str = env!("CARGO_PKG_VERSION_MAJOR");
pub const VERSION_MINOR: &'static str = env!("CARGO_PKG_VERSION_MINOR");
pub const VERSION_PATCH: &'static str = env!("CARGO_PKG_VERSION_PATCH");
pub const VERSION_TAGS: Option<&'static str> = option_env!("CARGO_PKG_VERSION_TAGS");
pub const VERSION_HASH: &'static str = env!("CARGO_PKG_HASH");
pub const VERSION_TIMESTAMP_RFC3339: &'static str = env!("CARGO_PKG_TIMESTAMP_RFC3339");

pub fn OUSIA_PATH_FROM_ENV() -> Option<PathBuf> {
    var_os("OUSIA_PATH").map(|s| PathBuf::from(s))
}


pub const SUBCOMMANDS_FST: &'static str = "subcommands.fst";
