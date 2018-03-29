use core::parser::ast::Ast;

use std::path::PathBuf;

use clap::ArgMatches;
use exitcode;
use exitcode::ExitCode;


pub fn main(subcmd_matches: &ArgMatches) -> ExitCode {
    println!(
        "{:?}",
        Ast::from_file(PathBuf::from(subcmd_matches.value_of("path").unwrap()))
    );
    exitcode::OK
}
