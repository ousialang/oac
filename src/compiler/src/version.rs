pub const MAJOR: &'static str = env!("CARGO_PKG_VERSION_MAJOR");
pub const MINOR: &'static str = env!("CARGO_PKG_VERSION_MINOR");
pub const PATCH: &'static str = env!("CARGO_PKG_VERSION_PATCH");
pub const COMMIT_HASH: &'static str = env!("CARGO_PKG_COMMIT_HASH");
pub const RELEASE_DATE: &'static str = env!("CARGO_PKG_RELEASE_DATE_RFC3339");
pub const VERBOSE: &'static str = concat!(
    'v',
    env!("CARGO_PKG_VERSION_MAJOR"),
    '.',
    env!("CARGO_PKG_VERSION_MINOR"),
    '.',
    env!("CARGO_PKG_VERSION_PATCH"),
    " @ ",
    env!("CARGO_PKG_COMMIT_HASH"),
);
