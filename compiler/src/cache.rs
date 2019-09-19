use std::path::Path;

pub struct Cache {
    //sqlite: rusqlite::Connection,
}

impl Cache {
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Cache, ()> {
        //rusqlite::Connection::open(path).map(|connection| Cache { sqlite: connection })
        Ok(Cache{})
    }
}
