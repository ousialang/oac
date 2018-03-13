
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
    tags: Vec<&'static str>,
    hash: &'static str,
    timestamp: SteadyTime,
}

const OUSIA_VERSION: OusiaVersion = OusiaVersion {
    major: env!("CARGO_PKG_VERSION_MAJOR").parse().unwrap(),
    minor: env!("CARGO_PKG_VERSION_MINOR").parse().unwrap(),
    patch: env!("CARGO_PKG_VERSION_PATCH").parse().unwrap(),
    tags: env!("CARGO_PKG_TAGS").split("-").collect(),
    hash: env!("CARGO_PKG_HASH"),
    timestamp: SteadyTime::now(), // FIXME
};

fn main() {
    exit(commander::main() as i32);
}
