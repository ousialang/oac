pub mod cache;
pub mod core;
pub mod feedback;
pub mod hub;
pub mod pass;
pub mod resources;
pub mod usage;

use std::process;
use std::convert::TryFrom;
use usage::clap_app;
use hub::Config;

fn main() -> ! {
    process::exit(match clap_app().get_matches().subcommand() {
        (usage::BUILD, Some(args)) => {
            let config = Config::try_from(args).unwrap();
            exitcode::OK
        }
        _ => exitcode::USAGE,
    })
}

pub const VERSION: &str = concat!(
    env!("CARGO_PKG_VERSION_MAJOR"),
    '.',
    env!("CARGO_PKG_VERSION_MINOR"),
    '.',
    env!("CARGO_PKG_VERSION_PATCH"),
    "-",
    env!("CARGO_PKG_COMMIT_HASH"),
    "+",
    env!("CARGO_PKG_TIMESTAMP"),
);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn version_is_semver() {
        assert!(semver::Version::parse(VERSION).is_ok());        
    }
}