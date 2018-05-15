// cli.rs
// ======
//
// A Command Line Interface (CLI) powered by 'clap'.

use clap::{App, AppSettings, Arg, SubCommand};
pub use cli::error::Error;

pub fn cli() -> App<'static, 'static> {
    App::new("oa")
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::ColorNever)
        .setting(AppSettings::AllowExternalSubcommands)
        .arg(
            Arg::with_name(version::VERSION)
                .short("V")
                .long(version::VERSION),
        )
        .arg(Arg::with_name(help::HELP).short("h").long(help::HELP))
        .subcommand(SubCommand::with_name(build::BUILD))
        .subcommand(
            SubCommand::with_name(doo::DOO).arg(Arg::with_name(doo::TASK).index(1).required(true)),
        )
        .subcommand(SubCommand::with_name(help::HELP).arg(Arg::with_name(help::TOPIC).index(1)))
        .subcommand(
            SubCommand::with_name(version::VERSION)
                .arg(
                    Arg::with_name(version::MAJOR)
                        .short("M")
                        .long(version::MAJOR),
                )
                .arg(
                    Arg::with_name(version::MINOR)
                        .short("m")
                        .long(version::MINOR),
                )
                .arg(
                    Arg::with_name(version::PATCH)
                        .short("p")
                        .long(version::PATCH),
                )
                .arg(Arg::with_name(version::TAGS).short("t").long(version::TAGS))
                .arg(
                    Arg::with_name(version::COMMIT_HASH)
                        .short("c")
                        .long(version::COMMIT_HASH),
                )
                .arg(
                    Arg::with_name(version::RELEASE_DATE_RFC3339)
                        .short("r")
                        .long(version::RELEASE_DATE_RFC3339),
                )
                .arg(Arg::with_name(version::ALL).short("a").long(version::ALL)),
        )
}

pub mod build {
    pub const BUILD: &'static str = "build";
}

pub mod doo {
    pub const DOO: &'static str = "do";
    pub const TASK: &'static str = "task";
}

pub mod help {
    pub const HELP: &'static str = "help";
    pub const TOPIC: &'static str = "topic";
}

pub mod version {
    pub const VERSION: &'static str = "version";
    pub const MAJOR: &'static str = "major";
    pub const MINOR: &'static str = "minor";
    pub const PATCH: &'static str = "patch";
    pub const TAGS: &'static str = "tags";
    pub const COMMIT_HASH: &'static str = "commit-hash";
    pub const RELEASE_DATE_RFC3339: &'static str = "release-date-rfc3339";
    pub const ALL: &'static str = "all";
}

pub mod error {
    use clap;
    use std::error;
    use std::fmt;

    #[derive(Debug)]
    pub struct Error {
        clap_error: clap::Error,
    }

    impl error::Error for Error {
        fn description(&self) -> &str {
            // At the time of writing, 'Error::description()' has just been deprecated in favor of
            // 'Display::fmt()', so we just spit out Clap's error message.
            &self.clap_error.message[..]
        }
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.clap_error.message)
        }
    }

    impl From<clap::Error> for Error {
        fn from(err: clap::Error) -> Self {
            Error { clap_error: err }
        }
    }
}
