use clap::{App, AppSettings, Arg, SubCommand};
use crate::VERSION;
use crate::hub::Config;
use std::convert::TryFrom;

pub const BUILD: &str = "build";
pub const SOURCE: &str = "source";
pub const TARGET: &str = "target";

pub fn clap_app() -> App<'static, 'static> {
    App::new("The Ousia reference compiler")
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::ColorNever)
        .version(VERSION)
        .subcommand(
            SubCommand::with_name(BUILD)
                .arg(Arg::with_name(SOURCE).short("s"))
                .arg(Arg::with_name(TARGET).short("t"))
                .arg(Arg::with_name(BUILD).short("b")),
        )
        .subcommand(SubCommand::with_name("help"))
        .subcommand(SubCommand::with_name("version"))
}

impl TryFrom<&clap::ArgMatches<'_>> for Config {
    type Error = ();

    fn try_from(args: &clap::ArgMatches) -> Result<Self, Self::Error> {
        Ok(Self::default())
    }
}