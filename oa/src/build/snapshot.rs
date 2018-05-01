use std::path::Path;

use blake2::{Blake2b, Digest};
use fuse::FileAttr;

struct Snapshot {
    len: u64,
    signature: Signature,
}

enum Signature {
    Blake2b([u8]),
    LastModified(SystemTime),
}

impl Snapshot {
    fn new(path: Path) -> Result<Self, Error> {
        let metadata = fs::metadata(path)?;

        Snapshot {
            len: metadata.len(),
            signature: metadata.modified().or(),
        }
    }
}
