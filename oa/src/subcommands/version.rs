use constants;
use utils::feedback::Level;

use clap::ArgMatches;
use exitcode;
use exitcode::ExitCode;


pub fn main(matches: ArgMatches) -> ExitCode {
    let version = OUSIA_VERSION();
    match matches.args.len() {
        0 => print_human_readable_version(),
        _ => print_machine_readable_version(),
    }
    exitcode::OK
}

fn print_human_readable_version() {
    let hyphenated_tags = {
        if constants::VERSION_TAGS.is_empty() {
            "".to_owned()
        } else {
            constants::VERSION_TAGS.join("-")
        }
    };
    println!("Ousia {}.{}.{}{} ({})",
        constants::VERSION_MAJOR,
        constants::VERSION_MINOR,
        constants::VERSION_PATCH,
        hyphenated_tags,
        constants::VERSION_HASH,
    );
}

fn print_machine_readable_version() {
    // TODO
}
