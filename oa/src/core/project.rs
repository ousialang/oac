use std::path::path;

struct Project {
    path: Path,
}

impl Project {

    fn new(path: Path): Option<Project> {
        if path.is_dir() {

        } else if path.is_file() {

        } else {
            None
        }
    }
}
