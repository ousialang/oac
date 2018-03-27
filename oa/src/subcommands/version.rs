use constants::{OUSIA_VERSION, OusiaVersion};
use utils::feedback::Level;

use clap::ArgMatches;
use exitcode;
use exitcode::ExitCode;


pub fn main(matches: ArgMatches) -> ExitCode {
    let version = OUSIA_VERSION();
    match matches.args.len() {
        0 => print_human_readable_version(version),
        _ => print_machine_readable_version(version),
    }
    exitcode::OK
}

fn print_human_readable_version(version: OusiaVersion) {
    let version_hyphenated_tags = {
        if version.tags.is_empty() {
            "".to_owned()
        } else {
            version.tags.join("-")
        }
    };
    println!("Ousia {}.{}.{}{} ({})",
        version.major,
        version.minor,
        version.patch,
        version_hyphenated_tags,
        version.hash,
    );
}

fn print_machine_readable_version(version: OusiaVersion) {
    // TODO
}
