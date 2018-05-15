// version.rs
// ==========
//
// A subcommand for displaying the currently installed Ousia release in both human- and machine-
// readable formats.

use clap::ArgMatches;
use cli;
use exitcode::{self, ExitCode};

pub fn main(args: ArgMatches) -> ExitCode {
    if args.args.is_empty() {
        println!("Ousia {}", verbose());
    } else {
        if args.is_present(cli::version::MAJOR) {
            println!("{}: {}", cli::version::MAJOR, *constants::MAJOR);
        }
        if args.is_present(cli::version::MINOR) {
            println!("{}: {}", cli::version::MINOR, *constants::MINOR);
        }
        if args.is_present(cli::version::PATCH) {
            println!("{}: {}", cli::version::PATCH, *constants::PATCH);
        }
        if args.is_present(cli::version::TAGS) {
            println!("{}: {}", cli::version::TAGS, (*constants::TAGS).join(" "));
        }
        if args.is_present(cli::version::COMMIT_HASH) {
            println!("{}: {}", cli::version::COMMIT_HASH, *constants::COMMIT_HASH);
        }
        if args.is_present(cli::version::RELEASE_DATE_RFC3339) {
            println!(
                "{}: {}",
                cli::version::RELEASE_DATE_RFC3339,
                (*constants::RELEASE_DATE).to_rfc3339()
            );
        }
    }
    exitcode::OK
}

pub fn major_dot_minor_dot_patch() -> String {
    format!(
        "{}.{}.{}",
        *constants::MAJOR,
        *constants::MINOR,
        *constants::PATCH
    )
}

pub fn verbose() -> String {
    format!(
        "{}:{}{}{}",
        major_dot_minor_dot_patch(),
        *constants::COMMIT_HASH,
        if (*constants::TAGS).is_empty() {
            "-"
        } else {
            ""
        },
        (*constants::TAGS).join("-"),
    )
}

pub mod constants {
    use chrono::{DateTime, FixedOffset};

    lazy_static! {
        pub static ref MAJOR: u16 = env!("CARGO_PKG_VERSION_MAJOR").parse().unwrap();
        pub static ref MINOR: u16 = env!("CARGO_PKG_VERSION_MINOR").parse().unwrap();
        pub static ref PATCH: u16 = env!("CARGO_PKG_VERSION_PATCH").parse().unwrap();
        pub static ref TAGS: Vec<&'static str> = {
            option_env!("CARGO_PKG_VERSION_TAGS")
                .unwrap_or("")
                .split(" ")
                .collect()
        };
        pub static ref COMMIT_HASH: &'static str = env!("CARGO_PKG_COMMIT_HASH");
        pub static ref RELEASE_DATE: DateTime<FixedOffset> =
            { DateTime::parse_from_rfc3339(env!("CARGO_PKG_RELEASE_DATE_RFC3339")).unwrap() };
    }
}

#[cfg(test)]
mod test {
    use chrono::Utc;
    use version::constants;

    #[test]
    fn release_date_is_from_past() {
        assert!(*constants::RELEASE_DATE < Utc::now());
    }

    #[test]
    fn commit_hash_is_hexadecimal() {
        for c in *constants::COMMIT_HASH {
            assert!(c.is_ascii_hexdigit());
        }
    }

    #[test]
    fn commit_hash_is_nonempty() {
        assert!(!*constants::COMMIT_HASH.is_empty());
    }

    #[test]
    fn tags_are_ascii() {
        for tag in *constants::TAGS {
            assert!(tag.is_ascii());
        }
    }

    #[test]
    fn tags_are_nonempty() {
        for tag in *constants::TAGS {
            assert!(!tag.is_empty());
        }
    }
}
