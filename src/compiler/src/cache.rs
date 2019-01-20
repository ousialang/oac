use rusqlite;

use std::path::Path;

pub struct Cache {
    sqlite: rusqlite::Connection,
}

impl Cache {
    pub fn load<P: AsRef<Path>>(path: P) -> rusqlite::Result<Cache> {
        rusqlite::Connection::open(path).map(|connection| Cache { sqlite: connection })
    }
}
