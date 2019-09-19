use std::env;
use std::fs::File;
use std::io;
use std::path::PathBuf;

const ENV_VAR: &'static str = "OAC_RESOURCES";

pub struct Resources {
    location: PathBuf,
}

impl Resources {
    pub fn new(&mut self) -> Option<Resources> {
        env::var(ENV_VAR)
            .map(|var| Resources { location: PathBuf::from(var) })
            .ok()
    }

    pub fn config(&mut self) -> io::Result<File> {
        self.location.push("configs.toml");
        let result: io::Result<File> = File::open(&self.location);
        self.location.pop();
        result
    }
}
