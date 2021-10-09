mod scanner;

use clap::{App, AppSettings, Arg, SubCommand};

fn main() {
    match clap_app().get_matches().subcommand() {
        ("build", Some(args)) => {
            let path = args.value_of("source").unwrap();
            let s = std::fs::read_to_string(path).unwrap();
            let tokens = scanner::scan(s);
            println!("Tokens are {:?}", tokens);
        }
        _ => (),
    }
}

fn clap_app() -> App<'static, 'static> {
    App::new("The Ousia reference compiler")
        .setting(AppSettings::StrictUtf8)
        .setting(AppSettings::ColorNever)
        .version("0.1")
        .subcommand(
            SubCommand::with_name("build")
                .about("Builds a file with Ousia source code.")
                .arg(Arg::with_name("source"))
                .arg(Arg::with_name("target")),
        )
}
