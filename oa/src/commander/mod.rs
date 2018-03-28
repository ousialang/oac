use subcommands as subcmd;
use utils::feedback::Level;

use clap;
use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use exitcode;
use exitcode::ExitCode;


pub fn main() -> ExitCode {
    match clap_app().get_matches_safe() {
        Err(e) => CliUsageError::new(e).emit(),
        Ok(m) => {
            match m.subcommand() {
                ("help", Some(sub_m)) => subcmd::help::main(sub_m),
                ("version", Some(sub_m)) => subcmd::version::main(sub_m),
                ("fuck", Some(sub_m)) => subcmd::fuck::main(sub_m),
                (external, Some(_)) => exitcode::OK, // TODO
                (_, None) => {
                    if m.is_present("version") {
                        subcmd::version::main(&ArgMatches::new())
                    } else {
                        subcmd::help::main(&ArgMatches::new())
                    }
                }
                _ => exitcode::SOFTWARE,
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
        .subcommand(
            SubCommand::with_name("version")
                .arg(Arg::with_name("major").short("M").long("major"))
                .arg(Arg::with_name("minor").short("m").long("minor"))
                .arg(Arg::with_name("patch").short("p").long("patch"))
                .arg(Arg::with_name("tags").short("t").long("tags"))
                .arg(Arg::with_name("commit-hash").short("c").long("commit-hash")),
        )
        .subcommand(SubCommand::with_name("help").arg(
            Arg::with_name("topic").index(
                1,
            ),
        ))
        .subcommand(SubCommand::with_name("fuck").arg(
            Arg::with_name("issue").index(
                1,
            ),
        ))
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
