// main.rs
// =======
//
// Ousia'a driver program.

#![feature(custom_attribute)]

extern crate bincode;
extern crate chrono;
extern crate clap;
extern crate colored;
extern crate exitcode;
extern crate fst;
extern crate fst_levenshtein;
extern crate futures;
extern crate indexmap;
#[macro_use]
extern crate lazy_static;
extern crate num_cpus;
extern crate rayon;
#[macro_use]
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;
extern crate stopwatch;
extern crate termion;
extern crate textwrap;
extern crate toml;

pub mod build;
pub mod cli;
pub mod core;
pub mod disk;
//pub mod doo;
pub mod feedback;
//pub mod help;
//pub mod langserver;
//pub mod repl;
pub mod version;

use std::env;
use std::process;

fn main() -> ! {
    // First things first, locate the support files.
    if let Err(err) = disk::locate() {
        println!("{}", err);
    }
    let args: Vec<String> = env::args().collect();
    let matched_args = cli::cli().get_matches_from_safe(args);
    process::exit(match matched_args.map(|x| x.subcommand()) {
        //Ok(("do", Some(matched_subcmd_args))) => tasks::main(*matched_subcmd_args),
        //Ok(("langserver", Some(matched_subcmd_args))) => langserver::main(*matched_subcmd_args),
        //Ok(("help", Some(matched_subcmd_args))) => help::main(*matched_subcmd_args),
        //Ok(("repl", Some(matched_subcmd_args))) => repl::main(*matched_subcmd_args),
        Ok(("version", Some(matched_subcmd_args))) => version::main(*matched_subcmd_args),
        Ok((external_subcmd_name, None)) => {
            let command = process::Command::new(disk::subcommand_executable_path(
                external_subcmd_name,
            )).args(args);
            match command.status() {
                Ok(exit_code) => exit_code.code().unwrap_or(exitcode::SOFTWARE),
                Err(e) => exitcode::IOERR,
            }
        }
        Err(err) => {
            println!("{}", cli::Error::from(err));
            exitcode::USAGE
        }
    })
}
