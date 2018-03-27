use constants;

use clap::ArgMatches;
use exitcode;
use exitcode::ExitCode;


pub fn main(args: Option<ArgMatches>) -> ExitCode {
    match args {
        Some(some_args) => {
            match some_args.args.len() {
                0 => print_human_readable_version(),
                _ => print_machine_readable_version(),
            }
        }
        None => print_human_readable_version(),
    }
    exitcode::OK
}

fn print_human_readable_version() {
    println!("Ousia {}{}{} ({})",
        constants::VERSION,
        if constants::VERSION_TAGS.is_some() { "" } else { "-" },
        constants::VERSION_TAGS.map_or_else(|| String::new(), |s| s.replace(" ", "-")),
        constants::VERSION_HASH,
    );
}

fn print_machine_readable_version() {
    // TODO
}
