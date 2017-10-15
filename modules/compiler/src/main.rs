#[macro_use]
extern crate colored;

use colored::Colorize;
use std::collections::HashMap;
use std::env;
use std::io::{stdin, stdout, Write};

mod feedback;
mod scanner;

fn main() {
    let mut args = env::args_os();
    args.next();
    match args.next() {
        None => {
            repl();
        }
        Some(os_string) => {
            match os_string.into_string() {
                Err(_) => {
                    help();
                }
                Ok(s) => {
                    match s.to_lowercase().as_ref() {
                        "build" => {
                            build();
                        }
                        "help" => {
                            help();
                        }
                        "repl" => {
                            repl();
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    //(version: env!("CARGO_PKG_VERSION"))
    //(author: env!("CARGO_PKG_AUTHORS"))
    //        (about: "Builds an Ousia application from source"))
    //        (about: "Downloads and installs an Ousia package"))
    //        (about: "Starts an interactive session in the REPL"))
    //        (about: "Prints the current Ousia version"))
}

fn fetch_args(args: Vec<&str>) -> Option<HashMap<String, String>> {
    let hash_args = HashMap::new();
    let is_error: bool;
    for arg in args {
        /*if arg.chars().take(2).collect() == "--" {

        } else if arg.chars().take(1).collect() == '-' {
            let short_args: String = arg.chars().skip(1).collect();
            for letter in short_args.chars() {
                //hash_args.insert(letter.to_string(), String::new());
            }
        }*/
    }
    Some(hash_args)
}

pub fn build() {
    println!("Build OUSIA code");
}

pub fn help() {
    println!(
        "The Ousia programming language platform

Usage:
    ousia ‹command› ‹arguments?›

Available Ousia commands:
    build    Build OUSIA code
    help     Help
    repl     The Ousia REPL
    run      Runs some Ousia code"
    );
}

fn repl() {
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
        println!("{:?}", scanner::scan(&s));
    }

}
