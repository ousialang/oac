use std::env::home_dir;
use std::env::{var, var_os};
use std::path::PathBuf;


pub fn OUSIA_PATH_FROM_ENV() -> Option<PathBuf> {
    var_os("OUSIA_PATH").map(|s| PathBuf::from(s))
}

pub fn resource_path() -> PathBuf {
    match OUSIA_PATH_FROM_ENV() {
        Some(pathbuf) => pathbuf,
        None => {
            // Try the platform's default
            if cfg!(target_os = "macos") {
                PathBuf::from(r"/Library/Ousia/")
            } else if cfg!(target_os = "linux") {
                PathBuf::from(r"/usr/share/")
            } else if cfg!(target_os = "windows") {
                PathBuf::from(
                    var("%ProgramFiles(x86)%")
                        .or(var("%ProgramFiles%"))
                        .unwrap(),
                )
            } else {
                // FIXME: cfg evaluating to false
                home_dir().map_or_else(|| PathBuf::new(), |p| p.join(".oa/"))
            }
        }
    }
}
