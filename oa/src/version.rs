// version.rs
// ==========
//
// A subcommand for displaying the currently installed Ousia release in both human- and machine-
// readable formats.

use clap::ArgMatches;
use exitcode::{self, ExitCode};

pub fn main(args: ArgMatches) -> ExitCode {
    if args.args.is_empty() {
        println!("Ousia {}", verbose());
    } else {
        if args.is_present("major") {
            println!("major: {}", constants::MAJOR);
        }
        if args.is_present("minor") {
            println!("minor: {}", constants::MINOR);
        }
        if args.is_present("patch") {
            println!("patch: {}", constants::PATCH);
        }
        if args.is_present("tags") {
            println!("tags: {}", constants::TAGS.unwrap_or(""));
        }
        if args.is_present("commit-hash") {
            println!("commit-hash: {}", constants::COMMIT_HASH);
        }
        if args.is_present("release-date-rfc3339") {
            println!("release-date-rfc3339: {}", constants::RELEASE_DATE_RFC3339);
        }
    }
    exitcode::OK
}

pub fn major_dot_minor_dot_patch() -> String {
    format!("{}.{}.{}", MAJOR, MINOR, PATCH)
}

pub fn verbose() -> String {
    format!(
        "{}:{}{}{}",
        major_dot_minor_dot_patch(),
        constants::COMMIT_HASH,
        if constants::TAGS.is_some() { "-" } else { "" },
        constants::TAGS.map_or_else(|| String::new(), |s| s.replace(" ", "-")),
    )
}

pub mod constants {
    pub const MAJOR: &'static str = env!("CARGO_PKG_VERSION_MAJOR");
    pub const MINOR: &'static str = env!("CARGO_PKG_VERSION_MINOR");
    pub const PATCH: &'static str = env!("CARGO_PKG_VERSION_PATCH");
    pub const TAGS: Option<&'static str> = option_env!("CARGO_PKG_VERSION_TAGS");
    pub const COMMIT_HASH: &'static str = env!("CARGO_PKG_COMMIT_HASH");
    pub const RELEASE_DATE_RFC3339: &'static str = env!("CARGO_PKG_RELEASE_DATE_RFC3339");
}

#[cfg(test)]
mod test {
    use version::constants;

    use chrono::Utc;

    #[test]
    fn release_date_rfc3339_adehers_to_iso8601_and_is_from_past() {
        let release_date = DateTime::parse_from_rfc3339(constants::RELEASE_DATE_RFC3339);
        assert!(release_date.is_ok());
        // Technically, Chrono is not monotonic
        assert!(release_date.unwrap() < Utc::now());
    }

    #[test]
    fn commit_hash_is_hexadecimal() {
        assert!(constants::COMMIT_HASH.is_ascii_hexdigit());
    }

    #[test]
    fn commit_hash_is_nonempty() {
        assert!(!constants::COMMIT_HASH.is_empty());
    }
}
