extern crate colored;

use self::colored::*;

pub enum Level {
    Fatal,
    Error,
    Warning,
    Note,
    Log,
}

impl Level {
    pub fn to_colored_string(self) -> ColoredString {
        match self {
            Level::Fatal => "FATAL".red().bold(),
            Level::Error => "ERROR".red().bold(),
            Level::Warning => "WARNING".yellow().bold(),
            Level::Note => "NOTE".bold(),
            Level::Log => "LOG".normal(),
        }
    }
}

pub struct Feedback {
    id: u32,
    level: Level,
    message: String,
}
