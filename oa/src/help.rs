// help.rs
// =======
//
// A pager-based 'help' subcommand.

use disk;
use feedback;

use std::fs::File;
use std::io::prelude::*;

use clap::ArgMatches;
use exitcode::{self, ExitCode};
use serde_json;

pub fn main(args: ArgMatches) -> ExitCode {
    let query = args.value_of("topic").unwrap();
    let settings = Settings::local();
    match Topic::find(query) {
        Ok(topic) => {
            topic.show();
            exitcode::OK
        }
        Err(e) => {
            println!(
                "{} There is no manual entry for the query '{}'",
                *feedback::FATAL,
                query
            );
            exitcode::UNAVAILABLE
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Settings {
    pager: String,
}

impl Settings {
    fn local() -> Result<Self, DiskError> {
        disk::subcommand_settings("help")?;
    }
}

impl Default for Settings {
    fn default() -> Self {
        Settings { pager: "more" }
    }
}

#[derive(Serialize, Deserialize)]
struct Topic {
    name: String,
    kind: TopicKind,
    path: String,
}

#[derive(Serialize, Deserialize)]
enum TopicKind {
    Resource,
    Task,
}

impl Topic {
    fn locate(query: String) -> Result<Option<Self>, disk::Error> {
        let mut path = disk::subcommand_path_in_prefix_dir("help");
        path.push("topics");
        path.push(query);
        if path.exists() {
            let mut contents = String::new();
            let f = File::open(path)?;
            f.read_to_string(&mut contents);
            let topic: Topic = serde_json::from_str(contents)?;
            Ok(Some(topic))
        } else {
            OK(None)
        }
    }
}
