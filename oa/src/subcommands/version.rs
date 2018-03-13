extern crate getopts;
extern crate sysexit;

use commander::Subcommand;
use ::OUSIA_VERSION;
use utils;

pub const Version: Subcommand = Subcommand::Embedded {
    schema: Options::new()
                    .getopt(),
    entry_point: entry_point,
};

fn handle_unknown_arg(option: String) {
    println!("{} {} is not a known option.", utils::io::FATAL, option);
}

fn entry_point(matches: getopts::Matches) -> sysexit::Code {
    match matches.len() {
        0 => print_human_readable_version(),
        _ => print_machine_readable_version(),
    }
    sysexit::Success
}

fn print_human_readable_version() {
    println!("Ousia {}.{}.{}-{} ({})",
        OUSIA_VERSION.major,
        OUSIA_VERSION.minor,
        OUSIA_VERSION.patch,
        OUSIA_VERSION.tag.join("-"),
        OUSIA_VERSION.build,
    );
}

fn print_machine_readable_version() {
    // TODO
}
