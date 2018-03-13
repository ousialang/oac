extern crate clap;

use clap::{App, AppSettings};

let mut clap_app = App::new("")
    .setting(AppSettings::StrictUtf8)
    .setting(AppSettings::VersionlessSubcommands)
    .setting(AppSettings::DisableHelpSubcommand)
    .setting(AppSettings::DisableVersion);
    .subcommand(SubCommand::with_name("beautify")
        .arg(Arg::with_name("dry-run")
             .short("d")
             .long("--dry-run")
             .takes_value(true)))
    .subcommand(SubCommand::with_name("help")
        .arg(Arg::with_name("topic")
             .required(true)
             .takes_value(true)))
    .subcommand(SubCommand::with_name("version")
        .arg(Arg::with_name("major")
             .short("M")
             .long("major"))
        .arg(Arg::with_name("minor")
             .short("m")
             .long("minor"))
        .arg(Arg::with_name("patch")
             .short("p")
             .long("patch"))
        .arg(Arg::with_name("tags")
             .short("t")
             .long("tags"))
        .arg(Arg::with_name("build")
             .short("b")
             .long("build")));
