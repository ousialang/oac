#[macro_use]
extern crate clap;

use std::io::{stdin, stdout, Write};

mod reader;

fn main() {
    let matches = clap_app!(ousia =>
        (version: env!("CARGO_PKG_VERSION"))
        (author: env!("CARGO_PKG_AUTHORS"))
        (@subcommand build =>
            (about: "Builds an Ousia application from source"))
        (@subcommand install =>
            (about: "Downloads and installs an Ousia package"))
        (@subcommand repl =>
            (about: "Starts an interactive session in the REPL"))
        (@subcommand version =>
            (about: "Prints the current Ousia version"))
    ).get_matches();

    if let Some(_) = matches.subcommand_matches("build") {
        println!("Build is not yet implemented!");
    }
    if let Some(_) = matches.subcommand_matches("repl") {
        println!(
            "Ousia {}.{}\n",
            env!("CARGO_PKG_VERSION_MAJOR"),
            env!("CARGO_PKG_VERSION_MINOR")
        );
        loop {
            let mut s = String::new();
            print!("ousia› ");
            stdout().flush();
            stdin().read_line(&mut s).expect(
                "Uh oh, something wen wrong :(",
            );
            if let Some('\n') = s.chars().next_back() {
                s.pop();
            }
            if let Some('\r') = s.chars().next_back() {
                s.pop();
            }
            println!("  {}", s);
            reader::tokenize(&s);
        }
    }
}
