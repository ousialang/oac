// doo.rs
// =======
//
// The 'do' command provides a straightforward task runner.

use clap::ArgMatches;
use cli;
use disk;
use doo::error::Error;
use exitcode::{self, ExitCode};
use feedback;
use serde_json;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::Command;

pub fn main(args: ArgMatches) -> ExitCode {
    let task_name = args.value_of(cli::doo::TASK).unwrap();
    let task = match Task::find(task_name) {
        Ok(Some(t)) => t,
        Ok(None) => {
            println!("{}", "Not found");
            return exitcode::UNAVAILABLE;
        }
        Err(err) => {
            return exitcode::IOERR;
        }
    };
    let child = match task.command().spawn() {
        Ok(child) => child,
        Err(_) => return exitcode::IOERR,
    };
    let exit_status = match child.wait() {
        Ok(exit_status) => exit_status,
        Err(_) => return exitcode::IOERR,
    };
    exit_status.code().unwrap_or(exitcode::IOERR)
}

#[derive(Serialize, Deserialize)]
struct Task {
    name: String,
    path_to_executable: String,
    args: Vec<String>,
    until: Event,
}

impl Task {
    fn find(name: &str) -> Result<Option<Task>, Error> {
        let path = Task::path_to_definition_file(name);
        if path.exists() {
            let file = fs::File::open(path)?;
            Ok(Some(serde_json::from_reader(file)?))
        } else {
            Ok(None)
        }
    }

    fn true_path_to_executable(&self) -> PathBuf {
        PathBuf::from(self.path_to_executable)
    }

    fn save_definition(&self) -> Result<(), Error> {
        let path_to_definition = Task::path_to_definition_file(&self.name);
        // It's technically possible that a race condition occurs and that the file is created
        // right after checking that it doesn't exist and before actually creating it.
        // We don't have to worry about such scenario as 'File::create' will truncate its contents.
        let file = fs::File::create(path_to_definition)?;
        serde_json::to_writer(file, self)?;
        Ok(())
    }

    fn command(&self) -> Command {
        let absolute_path_to_executable = {
            if self.true_path_to_executable().is_relative() {
                let path = disk::subcommand_path_in_prefix_dir(cli::doo::DOO);
                path.push("executables");
                path.push(self.path_to_executable);
                path
            } else {
                PathBuf::from(self.path_to_executable)
            }
        };
        *Command::new(absolute_path_to_executable).args(self.args)
    }

    fn path_to_definition_file(task_name: &str) -> PathBuf {
        let path = path_of_tasks();
        path.push(task_name);
        path.set_extension(".json");
        path
    }
}

fn path_of_tasks() -> PathBuf {
    let path = disk::subcommand_path_in_prefix_dir(cli::doo::DOO);
    path.push("tasks");
    path
}

#[derive(Serialize, Deserialize)]
enum Event {
    Time,
    SomeTaskIsRun,
}

pub mod error {
    use colored::*;
    use exitcode::{self, ExitCode};
    use feedback;
    use serde_json;
    use std::convert::From;
    use std::error;
    use std::fmt;
    use std::io;

    #[derive(Debug)]
    pub enum Error {
        Io(io::Error),
        Serde(serde_json::Error),
    }

    impl Error {
        fn suggested_exit_code(&self) -> ExitCode {
            match self {
                Error::Io(_) => exitcode::IOERR,
                Error::Serde(_) => exitcode::CONFIG,
            }
        }
    }

    impl error::Error for Error {
        fn description(&self) -> &str {
            "FIXME"
        }
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", *feedback::FATAL);
            match self {
                Error::Io(err) => write!(f, "IO error: {}", err),
                Error::Serde(err) => write!(f, "Missing resources"),
            }
        }
    }

    impl From<io::Error> for Error {
        fn from(err: io::Error) -> Self {
            Error::Io(err)
        }
    }

    impl From<serde_json::Error> for Error {
        fn from(err: serde_json::Error) -> Self {
            Error::Serde(err)
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn save_with_relative_path() {
        let task = Task {
            name: "foobar",
            path_to_executable: "test.py",
            args: Vec::new(),
        };
    }

    #[test]
    fn save_with_absolute_path() {
        let task = Task {
            name: "foobar",
            path_to_executable: "test.py",
            args: Vec::new(),
        };
    }

    #[test]
    fn save_non_unicode() {}
}
