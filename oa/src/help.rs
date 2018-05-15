// help.rs
// =======
//
// A pager-based 'help' subcommand.

use clap::ArgMatches;
use disk;
use exitcode::{self, ExitCode};
use feedback;
use serde_json;
use std::fs::File;
use std::io::prelude::*;

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
    fn local() -> Result<Self, disk::error::Error> {
        disk::subcommand_settings("help")?;
    }
}

impl Default for Settings {
    fn default() -> Self {
        Settings {
            pager: "more".to_string(),
        }
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
    fn locate(query: String) -> Result<Option<Self>, disk::error::Error> {
        let mut path = disk::subcommand_path_in_prefix_dir("help");
        path.push("topics");
        path.push(query);
        if path.exists() {
            let mut contents = String::new();
            let f = File::open(path)?;
            f.read_to_string(&mut contents);
            let topic: Topic = serde_json::from_str(&contents)?;
            Ok(Some(topic))
        } else {
            Ok(None)
        }
    }
}
