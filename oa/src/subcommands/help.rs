extern crate getopts;
extern crate sysexit;

use self::getopts::Options;

use commander::Subcommand;

pub const Help: Subcommand = Subcommand::Embedded {
    schema: Options::new(),
    entry_point: Box::new(entry_point),
};

fn entry_point(args: getopts::Matches) -> sysexit::Code {
	sysexit::Success
}
