// repl.rs
// =======
//
// A Read-Eval-Print Loop (REPL) for Ousia. The REPL itself is just a fancy wrapper around
// 'core::Engine', which provides completition, highlighting, and other cool features.

mod ui;

use disk;
use langserver::LangServer;
use repl::ui::Ui;

use std::fs::File;

use clap::ArgMatches;
use colored::ColoredString;
use exitcode::{self, ExitCode};
use futures::prelude::Future;
use termion::event::{Event, Key};

pub fn main(args: ArgMatches) -> ExitCode {
    let mut repl = Repl::new();
    repl.exit_code.wait();
    exitcode::OK
}

const prompt: ColoredString = "=> ".bold();

pub struct Repl {
    history: Vec<String>,
    langserver: LangServer,
    ui: Ui,
    exit_code: Future<Item = ExitCode, Error = ExitCode>,
}

impl Repl {
    fn new() -> Self {
        Repl {
            history: Vec::new(),
            langserver: LangServer::new(),
            ui: Ui::new(),
            exit_code: Ok(exitcode::OK),
        }
    }

    fn exit_gracefully(&mut self) {
        self.stdout.flush().unwrap();
    }
}
