// repl.rs
// =======
//
// A Read-Eval-Print Loop (REPL) for Ousia. The REPL itself is just a fancy wrapper around
// 'core::Engine', which provides completition, highlighting, and other cool features.

mod ui;

use clap::ArgMatches;
use colored::*;
use disk;
use exitcode::{self, ExitCode};
use futures::prelude::Future;
use langserver::LangServer;
use repl::ui::Ui;
use std::fs::File;
use termion::event::{Event, Key};

pub fn main(args: ArgMatches) -> ExitCode {
    let mut repl = Repl::new();
    exitcode::OK
}

const PROMPT: ColoredString = "=> ".bold();

pub struct Repl {
    history: Vec<String>,
    langserver: LangServer,
    ui: Ui,
}

impl Repl {
    pub fn new() -> Self {
        Repl {
            history: Vec::new(),
            langserver: LangServer::new().unwrap(), // FIXME
            ui: Ui::new(),
        }
    }
}
