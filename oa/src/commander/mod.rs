extern crate getopts;
extern crate sysexit;

mod spellcheck;

use subcommands;
use utils::io::FATAL;
use utils::resources::resource_path;
use std::collections::HashMap;
use std::env::{args, Args};
use std::fs::File;
use std::path::Path;
use std::process::Command;

use sysexit::Code as ExitCode;

fn print_usage() -> ExitCode {
    let usage_message_path = resource_path(vec!["usage.txt".to_owned()]);
    let file = File::open(&usage_message_path);
    let mut usage_message = String::new();
    file.read_to_string(usage_message).expect(
        "Reading resource file",
    );
    //let available_commands = serde_json::from_str(usage_message)?;
	/*Commands* commands = available_commands();
	if (!commands) { return EX_UNAVAILABLE; }
	println!("Usage: ousia <command> [options] [<arguments>]\n\nCheck out these subcommands:");
	for cmd in commands {
        println!("  - {}", cmd.name.bold());
        println!("    {}", cmd.short_description());
	}
    println!("");
    println!("Type 'ousia help <command>' for more information about a command.");*/
    sysexit::Success
}

fn validate_args(args: Args, schema: getopts::Options) -> Result<getopts::Matches, ExitCode> {
    match schema.parse(args) {
        Err(getopts::Fail::UnrecognizedOption(o)) => Err(handle_unknown_option(o)),
        Err(getopts::Fail::OptionDuplicated(o)) => Err(handle_duplicated_option(o)),
        Err(getopts::Fail::UnexpectedArgument(a)) => Err(handle_unexpected_argument(a)),
        Ok(matches) => Ok(matches),
        _ => panic!("something unexpected"),
    }

}

fn handle_unknown_option(option: String) {
    println!("{}: '{}' is not a valid option.",
             FATAL,
             option,
    );
}

fn handle_duplicated_option(option: String) {
    println!("{}: the option '{}' was given more than once.",
             FATAL,
             option,
    );
}

fn handle_unexpected_argument(option: String) {
    println!("// TODO");
}

#[derive(Clone)]
pub enum Subcommand {
    Plugin { path: &'static Path },
    Embedded {
        schema: getopts::Options,
        entry_point: Box<Fn(getopts::Matches) -> ExitCode>,
    },
}

impl Subcommand {
    fn run(&self, args: Args) -> ExitCode {
        match self {
            Subcommand::Embedded {
                schema,
                entry_point,
            } => entry_point(schema.parse_options(args)),
            Subcommand::Plugin {
                path,
                sanitized_args,
            } => Command::new(path).args(args).spawn().unwrap().wait(),
        }
    }

    fn new(name: String) -> Option<Subcommand> {
        Subcommand::from_embedded_table(name).or_else(Subcommand::from_resources(name))
    }

    fn from_resources(name: String) -> Option<Subcommand> {
        let mut path = resource_path(vec!["plugins"], name);
        if path.exists() {
            Ok(Subcommand::Plugin { path: path })
        } else {
            None
        }
    }

    fn from_embedded_table(name: String) -> Option<Subcommand> {
        EMBEDDED_SUBCOMMANDS.get(name)
    }
}

const EMBEDDED_SUBCOMMANDS: HashMap<&'static str, Subcommand> =
    [
        //("fuck", subcommands::fuck::Fuck),
        ("help", subcommands::help::Help),
        ("version", subcommands::version::Version),
    ].iter()
        .cloned()
        .collect();

pub fn main() -> ExitCode {
    let args = args().collect();
    let subcmd_name = args[0];
    match args.len() {
        1 => print_usage(),
        _ => {
            match Subcommand::new(subcmd_name) {
                Ok(subcmd) => subcmd.run(),
                None => spellcheck::spellcheck(subcmd_name),
            }
        }
    }
}
