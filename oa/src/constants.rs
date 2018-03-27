use std::env::var_os;
use std::path::PathBuf;


pub struct OusiaVersion {
    pub major: u16,
    pub minor: u16,
    pub patch: u16,
    pub tags: Vec<&'static str>,
    pub hash: &'static str,
    pub timestamp_rfc3339: &'static str,
}

pub fn OUSIA_VERSION() -> OusiaVersion {
    OusiaVersion {
        major: env!("CARGO_PKG_VERSION_MAJOR").parse().unwrap(),
        minor: env!("CARGO_PKG_VERSION_MINOR").parse().unwrap(),
        patch: env!("CARGO_PKG_VERSION_PATCH").parse().unwrap(),
        tags: env!("CARGO_PKG_TAGS").split("-").collect(),
        hash: env!("CARGO_PKG_HASH"),
        timestamp_rfc3339: env!("CARGO_PKG_TIMESTAMP_RFC3339"),
    }
}


pub fn OUSIA_PATH_FROM_ENV() -> Option<PathBuf> {
    var_os("OUSIA_PATH").map(|s| PathBuf::from(s))
}


pub const SUBCOMMANDS_FST: &'static str = "subcommands.fst";
