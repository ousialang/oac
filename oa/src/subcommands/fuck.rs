/*extern crate getopts;
extern crate sysexit;

use commander::Subcommand;
use ::OUSIA_VERSION;
use utils;

pub const Fuck: Subcommand = Subcommand::Embedded {
    name: "fuck",
    entry_point: entry_point,
};

fn entry_point(matches: getopts::Matches) -> sysexit::Code {
    sysexit::Success
}

type Task = Fn<String, sysexit::Code>;

fn add_task(task: Fn<String, sysexit::Code>, flag: Option<String>) {
    let mut file = File::open(resource_path(vec!["subcommands", "fuck", "tasks.json"]))?;
}

mod tasks {
}*/
