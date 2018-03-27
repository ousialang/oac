extern crate clap;
extern crate exitcode;
extern crate fst;
extern crate fst_levenshtein;

mod commander;
pub mod constants;
pub mod core;
pub mod subcommands;
pub mod utils;

use std::process::exit;


fn main() {
    exit(commander::main() as i32);
}
