// task.rs
// =======
//
// The 'do' command provides a straightforward task runner.

use disk;
use disk::error::Error;

use std::fs::{self, File};
use std::io::Error as IoError;
use std::path::PathBuf;
use std::process::Command;

use bincode;
use clap::ArgMatches;
use exitcode::{self, ExitCode};

pub fn main(args: ArgMatches) -> ExitCode {
    let task_name = args.value_of("task").unwrap();
    match Task::find(task_name).command().spawn() {
        Ok(child) => child.wait().unwrap_or(exitcode::IOERR),
        Err(_) => exitcode::IOERR,
    }
}

#[derive(Serialize, Deserialize)]
struct Task {
    name: String,
    path_to_executable: String,
    args: Vec<String>,
    until: Event,
}

impl Task {
    fn find(name: String) -> Result<Option<Task>, Error> {
        let path = disk::subcommand_path_in_prefix_dir("do")
            .push("tasks")
            .push(name);
    }

    fn save(&self) -> Result<(), Error> {
        let path_to_executable = {
            if self.path_to_executable.is_relative() {
                disk::subcommand_path_in_prefix_dir("do")
                    .push("executables")
                    .push(self.path_to_executable)
            } else {
                self.path_to_executable
            }
        };
        let path_to_executables = disk::subcommand_path_in_prefix_dir("do").push("executables");
        // It's technically possible that a race condition occurs and that the file is created
        // right after checking that it doesn't exist and before actually creating it.
        // We don't have to worry about such scenario as 'File::create' will truncate its contents.
        if path_to_executable.exists() {
            Err(Error::Duplicate)
        } else {
            let file = File::create(self.name)?;
            file.write(bincode::deserialize(self)?);
            Ok(())
        }
    }

    fn command(&self) -> Command {
        Command::new(self.path_to_executable).args(self.args)
    }

    fn rename(&mut self, new_name: String) -> Result<(), IoError> {
        let old_path = self.path_to_task();
        self.name = new_name;
        let new_path = self.path_to_task();
        fs::rename(old_path, new_path)?;
        Ok(())
    }

    fn path_to_task(&self) -> PathBuf {
        disk::subcommand_path_in_prefix_dir("do")
            .push("executables")
            .push(self.name + ".bincode")
    }
}

enum Event {
    Time,
    SomeTaskIsRun,
}

pub mod schemas {

    pub struct Task {}
}

pub mod error {

    use std::convert::From;
    use std::error::Error as ErrorTrait;
    use std::io::Error as IoError;

    use bincode::Error as BincodeError;

    pub enum Error {
        Duplicate,
        Io(IoError),
        Bincode(BincodeError),
    }

    impl From<IoError> for Error {
        fn from(err: IoError) -> Self {
            Error::Io(err)
        }
    }

    impl From<BincodeError> for Error {
        fn from(err: Error) -> Self {
            Error::Bincode(err)
        }
    }
}
