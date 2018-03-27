use subcommands as subcmd;
use utils::feedback::Level;

use clap;
use clap::{App, AppSettings, Arg, SubCommand};
use exitcode;
use exitcode::ExitCode;


pub fn main() -> ExitCode {
    match clap_app().get_matches_safe() {
        Err(e) => CliUsageError::new(e).emit(),
        Ok(args) => {
            if args.is_present("help") {
                subcmd::help::main(None)
            } else if args.is_present("version") {
                subcmd::version::main(None)
            } else {
                match args.subcommand_name() {
                    Some("help") => subcmd::help::main(Some(args)),
                    Some("version") => subcmd::version::main(Some(args)),
                    _ => exitcode::OK,
                }
            }
        }
    }
}

fn clap_app() -> App<'static, 'static> {
    // Clap provides a wonderful set of defaults for CLIs, but we want to provide a unified and
    // consistent UX: for this reason, we override all Clap's default emitters and helpers and just
    // use it as a parser.
    App::new("oa")
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::ColorNever)
        .setting(AppSettings::VersionlessSubcommands)
        .setting(AppSettings::DisableHelpSubcommand)
        .setting(AppSettings::AllowExternalSubcommands)
        .setting(AppSettings::VersionlessSubcommands)
        .arg(Arg::with_name("version").short("V").long("version"))
        .arg(Arg::with_name("help").short("h").long("help"))
        .subcommand(SubCommand::with_name("help"))
        .subcommand(SubCommand::with_name("version"))
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
