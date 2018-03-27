pub mod help;
pub mod version;

use utils::resources::resource_path;

use std::env::args;
use std::process::Command;

use clap::ArgMatches;
use exitcode::ExitCode;


pub fn run_external(arg_matches: ArgMatches) -> ExitCode {
    let subcmd_name = arg_matches.subcommand_name().unwrap();
    let path = resource_path().join("external").join(subcmd_name);
    Command::new(path)
        .args(args())
        .spawn()
        .unwrap()
        .wait()
        .unwrap()
        .code()
        .unwrap()
}
