// cli.rs
// ======
//
// A Command Line Interface (CLI) powered by 'clap'.

use clap::{App, AppSettings, Arg, SubCommand};

pub fn cli() -> App<'static, 'static> {
    App::new("oa")
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::ColorNever)
        .setting(AppSettings::AllowExternalSubcommands)
        .arg(Arg::with_name("version").short("V").long("version"))
        .arg(Arg::with_name("help").short("h").long("help"))
        .subcommand(
            SubCommand::with_name("build").arg(Arg::with_name("path").index(1).required(true)),
        )
        .subcommand(SubCommand::with_name("do").arg(Arg::with_name("task").index(1).required(true)))
        .subcommand(SubCommand::with_name("help").arg(Arg::with_name("topic").index(1)))
        .subcommand(
            SubCommand::with_name("version")
                .arg(Arg::with_name("major").short("M").long("major"))
                .arg(Arg::with_name("minor").short("m").long("minor"))
                .arg(Arg::with_name("patch").short("p").long("patch"))
                .arg(Arg::with_name("tags").short("t").long("tags"))
                .arg(Arg::with_name("commit-hash").short("c").long("commit-hash"))
                .arg(
                    Arg::with_name("release-date-rfc3339")
                        .short("r")
                        .long("release-date-rfc3339"),
                )
                .arg(Arg::with_name("all").short("a").long("all")),
        )
}

pub mod error {

    use std::error;
    use std::fmt::{self, Formatter, Result as FmtResult};

    use clap::Error as ClapError;

    #[derive(Debug)]
    pub struct Error {
        clap_error: ClapError,
    }

    impl error::Error for Error {
        fn description(&self) -> &str {
            match self.clap_error.kind() {
                _ => self.clap_error.message,
            }
        }
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut Formatter) -> FmtResult {
            match self.clap_error {
                Error::Io(ref err) => write!(f, "IO error: {}", err),
                Error::Parse(ref err) => write!(f, "Parse error: {}", err),
            }
        }
    }

    impl From<ClapError> for Error {
        fn from(clap_error: ClapError) -> Self {
            Error {
                clap_error: clap_error,
            }
        }
    }
}
