
#[macro_use]
extern crate phf;
extern crate time;

mod commander;
mod subcommands;
pub mod utils;

use time::SteadyTime;
use std::process::exit;

struct OusiaVersion {
    major: u16,
    minor: u16,
    patch: u16,
    tags: Vec<String>,
    hash: &'static str,
    timestamp: SteadyTime,
}

const OUSIA_VERSION: OusiaVersion = OusiaVersion {
    major: env!("CARGO_PKG_VERSION_MAJOR") as u16,
    minor: env!("CARGO_PKG_VERSION_MINOR") as u16,
    patch: env!("CARGO_PKG_VERSION_PATCH") as u16,
    tags: env!("CARGO_PKG_TAGS").split("-").collect(),
    hash: env!("CARGO_PKG_HASH"),
    timestamp: SteadyTime::now(),
};

fn main() {
    exit(commander::main());
}
