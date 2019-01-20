use clap::{App, AppSettings, Arg, SubCommand};
use version;

pub const BUILD: &'static str = "build";
pub const SOURCE: &'static str = "source";
pub const TARGET: &'static str = "target";

pub fn clap_app() -> App<'static, 'static> {
    App::new("Ousia")
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::ColorNever)
        .version(version::VERBOSE)
        .subcommand(
            SubCommand::with_name("build")
                .arg(Arg::with_name("source").short("s"))
                .arg(Arg::with_name("target").short("t"))
                .arg(Arg::with_name("build").short("b")),
        )
        .subcommand(SubCommand::with_name("help"))
        .subcommand(SubCommand::with_name("version"))
}
