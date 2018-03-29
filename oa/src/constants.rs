pub const VERSION: &'static str = env!("CARGO_PKG_VERSION");
pub const VERSION_MAJOR: &'static str = env!("CARGO_PKG_VERSION_MAJOR");
pub const VERSION_MINOR: &'static str = env!("CARGO_PKG_VERSION_MINOR");
pub const VERSION_PATCH: &'static str = env!("CARGO_PKG_VERSION_PATCH");
pub const VERSION_TAGS: Option<&'static str> = option_env!("CARGO_PKG_VERSION_TAGS");
pub const VERSION_HASH: &'static str = env!("CARGO_PKG_HASH");
pub const VERSION_TIMESTAMP_RFC3339: &'static str = env!("CARGO_PKG_TIMESTAMP_RFC3339");

pub const SUBCOMMANDS_FST: &'static str = "subcommands.fst";
