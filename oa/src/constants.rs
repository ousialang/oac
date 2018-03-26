use std::env::var_os;
use std::path::PathBuf;


pub const OUSIA_PATH: PathBuf = PathBuf::from(var_os("OUSIA_PATH"));

pub const SUBCOMMANDS_FST: &'static str = "subcommands.fst";
