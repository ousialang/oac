extern crate getopts;
extern crate sysexit;

use getopts::Options;

use commander::Subcommand;

pub const Help: Subcommand = Subcommand::Embedded {
    schema: Options::new(),
    entry_point: entry_point,
};

fn entry_point(args: &Vec<String>) -> sysexit::Code {
	sysexit::Success
}
