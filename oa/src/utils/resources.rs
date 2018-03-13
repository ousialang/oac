use std::env::var;
use std::path::{Path, PathBuf};

pub fn resource_path(components: Vec<String>) -> Path {
    let path = resource_path_prefix();
    for component in components {
        path.push(component);
    }
    path
}

fn resource_path_prefix() -> PathBuf {
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
    } /* else {
        compile_error!("unsupported OS")
    }*/
}
