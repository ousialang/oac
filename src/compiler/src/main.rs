extern crate clap;
extern crate colored;
extern crate exitcode;
extern crate hlua;
#[macro_use]
extern crate lazy_static;
extern crate rayon;
extern crate rusqlite;
extern crate serde;
extern crate textwrap;

pub mod cache;
pub mod core;
pub mod feedback;
pub mod hub;
pub mod pass;
pub mod resources;
pub mod usage;
pub mod version;

use std::process::exit;

use usage::clap_app;

fn main() -> ! {
    exit(match clap_app().get_matches().subcommand() {
        (usage::BUILD, Some(args)) => exitcode::OK,
        _ => exitcode::USAGE,
    })
}
