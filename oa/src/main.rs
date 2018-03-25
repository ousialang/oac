extern crate humantime;

mod commander;
mod subcommands;
pub mod utils;

use std::process::exit;

use time::SteadyTime;


struct OusiaVersion {
    major: u16,
    minor: u16,
    patch: u16,
    tags: Vec<&'static str>,
    hash: &'static str,
    timestamp_rfc3339: &'static str,
}

const OUSIA_VERSION: OusiaVersion = OusiaVersion {
    major: env!("CARGO_PKG_VERSION_MAJOR").parse().unwrap(),
    minor: env!("CARGO_PKG_VERSION_MINOR").parse().unwrap(),
    patch: env!("CARGO_PKG_VERSION_PATCH").parse().unwrap(),
    tags: env!("CARGO_PKG_TAGS").split("-").collect(),
    hash: env!("CARGO_PKG_HASH"),
    timestamp_rfc3339: env!("CARGO_PKG_RFC3339_TIMESTAMP"),
};


fn main() {
    exit(commander::main());
}
