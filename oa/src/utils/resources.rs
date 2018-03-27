use constants::OUSIA_PATH_FROM_ENV;

use std::env::var;
use std::path::{Path, PathBuf};


pub fn resource_path() -> PathBuf {
    OUSIA_PATH_FROM_ENV().unwrap() // TODO
}
/*
fn path_prefix() -> PathBuf {
     if cfg!(macos) {
        PathBuf::from(r"/Library/Ousia/")
    } else if cfg!(linux) {
        PathBuf::from(r"/usr/share/")
    } else if cfg!(windows) {
        PathBuf::from(
            var("%ProgramFiles(x86)%")
                .or_else(var("%ProgramFiles%"))
                .unwrap(),
        )
    } else {
        //TODO compile_error!("Unknown platform");
    }
}*/
