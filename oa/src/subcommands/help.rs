use utils::resources::resource_path;

use std::fs::File;
use std::io::prelude::*;

use clap::ArgMatches;
use exitcode;
use exitcode::ExitCode;


pub fn main(subcmd_matches: &ArgMatches) -> ExitCode {
    if subcmd_matches.is_present("topic") {
        println!("Topic not available"); // TODO
        exitcode::OK
    } else {
        print_usage()
    }
}

fn print_usage() -> ExitCode {
    let path = resource_path().join("usage.txt");
    let mut contents = String::new();
    match File::open(path) {
        Err(_) => exitcode::IOERR,
        Ok(mut f) => {
            match f.read_to_string(&mut contents) {
                Err(_) => exitcode::IOERR,
                Ok(_) => {
                    println!("{}", contents);
                    exitcode::OK
                }
            }
        }
    }
}
