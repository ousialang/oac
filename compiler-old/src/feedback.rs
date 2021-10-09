use colored::*;

use std::error;
use std::io;
use std::ops::Range;
use std::string::ToString;

pub enum Severity {
    FATAL,
    ERROR,
    WARNING,
    NOTE,
}

impl ToString for Severity {
    fn to_string(&self) -> String {
        (match self {
            Severity::FATAL => "FATAL".bright_red().bold(),
            Severity::ERROR => "ERROR".red().bold(),
            Severity::WARNING => "WARNING".yellow().bold(),
            Severity::NOTE => "NOTE".bold(),
        }).to_string()
    }
}

pub struct Feedback {
    severity: Severity,
    ranges: Vec<Range<u32>>,
    uri: String,
    line: u64,
}

pub trait View {
    fn show(self, content: Feedback) -> Result<(), Box<error::Error>>;
}

pub struct Logger<T: io::Write> {
    handle: T,
}

impl<T> Logger<T> where T: io::Write {
    pub fn new(handle: T) -> Logger<T> {
        Logger { handle: handle }
    }
}

impl<T> View for Logger<T> where T: io::Write {
    fn show(self, content: Feedback) -> Result<(), Box<error::Error>> {
        Ok(())
    }
}
