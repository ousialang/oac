use subcommands;
use utils::feedback::Level;

use clap;
use clap::{App, AppSettings};
use exitcode;
use exitcode::ExitCode;


pub fn main() -> ExitCode {
    let app = App::new("oa")
        .setting(AppSettings::AllowExternalSubcommands)
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::VersionlessSubcommands)
        .setting(AppSettings::DisableHelpSubcommand);
    match app.get_matches_safe() {
        Err(e) => CliUsageError::new(e).emit(),
        Ok(arg_matches) => {
            match arg_matches.subcommand_name() {
                Some("help") => subcommands::help::main(arg_matches),
                Some("version") => subcommands::version::main(arg_matches),
                _ => exitcode::OK,
            }
        }
    }
}


// We want to be consistent in error messages and general UX, so instead of
// using clap's default error emitter we define a custom one.
struct CliUsageError {
    clap_err: clap::Error,
}

impl CliUsageError {
    fn new(clap_err: clap::Error) -> CliUsageError {
        CliUsageError { clap_err: clap_err }
    }

    fn emit(self) -> ExitCode {
        println!(
            "{}",
            match self.clap_err.kind {
                // TODO: custom emitters
                // Fall back to clap's default
                _ => self.clap_err.message,
            }
        );
        exitcode::USAGE
    }
}


fn print_usage() -> ExitCode {
    /*let usage_message_path = resource_path(vec!["usage.txt".to_owned()]);
    let file = File::open(&usage_message_path);
    let mut usage_message = String::new();
    file.read_to_string(usage_message).expect(
        "Reading resource file",
    );
    //let available_commands = serde_json::from_str(usage_message)?;
	Commands* commands = available_commands();
	if (!commands) { return EX_UNAVAILABLE; }
	println!("Usage: ousia <command> [options] [<arguments>]\n\nCheck out these subcommands:");
	for cmd in commands {
        println!("  - {}", cmd.name.bold());
        println!("    {}", cmd.short_description());
	}
    println!("");
    println!("Type 'ousia help <command>' for more information about a command.");*/
    exitcode::OK
}

fn handle_unknown_option(option: &str) {
    println!("{}: '{}' is not a valid option.",
        Level::Fatal.to_colored_string(),
        option,
    );
}

fn handle_duplicated_option(option: &str) {
    println!("{}: the option '{}' was given more than once.",
        Level::Warning.to_colored_string(),
        option,
    );
}

fn handle_unexpected_argument(option: String) {
    println!("// TODO");
}
