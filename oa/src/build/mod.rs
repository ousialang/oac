mod engine;

use core::parser::ast::Ast;

use std::path::PathBuf;

use clap::ArgMatches;
use exitcode::{self, ExitCode};

pub fn main(args: ArgMatches) -> ExitCode {
    println!(
        "{:?}",
        Ast::from_file(PathBuf::from(args.value_of("path").unwrap()))
            .0
            .unwrap()
            .tokens
            .len()
    );
    exitcode::OK
}
