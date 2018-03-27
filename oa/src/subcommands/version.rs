use constants;

use clap::ArgMatches;
use exitcode;
use exitcode::ExitCode;


pub fn main(subcmd_matches: &ArgMatches) -> ExitCode {
    if subcmd_matches.args.is_empty() {
        print_human_readable_version()
    } else {
        print_machine_readable_version(subcmd_matches)
    }
    exitcode::OK
}

fn print_human_readable_version() {
    println!("Ousia {}{}{} ({})",
        constants::VERSION,
        if constants::VERSION_TAGS.is_some() { "-" } else { "" },
        constants::VERSION_TAGS.map_or_else(|| String::new(), |s| s.replace(" ", "-")),
        constants::VERSION_HASH,
    );
}

fn print_machine_readable_version(args: &ArgMatches) {
    if args.is_present("major") {
        println!("{}", constants::VERSION_MAJOR);
    }
    if args.is_present("minor") {
        println!("{}", constants::VERSION_MINOR);
    }
    if args.is_present("patch") {
        println!("{}", constants::VERSION_PATCH);
    }
    if args.is_present("tags") {
        println!("{}", constants::VERSION_TAGS.unwrap_or(""));
    }
    if args.is_present("commit-hash") {
        println!("{}", constants::VERSION_HASH);
    }
}
