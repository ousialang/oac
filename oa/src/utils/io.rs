extern crate colored;

use self::colored::*;

pub const FATAL: ColoredString = "FATAL".red().bold();
pub const ERROR: ColoredString = "ERROR".red().bold();
pub const WARNING: ColoredString = "WARNING".yellow().bold();
pub const NOTE: ColoredString = "NOTE".bold();
