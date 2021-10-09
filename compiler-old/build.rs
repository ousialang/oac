use std::process::Command;
use chrono::Utc;

fn set_rustc_var(key: &str, value: String) {
    println!("cargo:rustc-env={}={}", key, value);
}

fn git_commit_hash() -> String {
    let hash = Command::new("git")
        .args(&["rev-parse", "--short=8", "HEAD"])
        .output()
        .unwrap()
        .stdout;
    String::from_utf8(hash).unwrap().chars().collect()
}

fn main() {
    set_rustc_var("CARGO_PKG_COMMIT_HASH", git_commit_hash());
    set_rustc_var(
        "CARGO_PKG_TIMESTAMP",
        Utc::now().format("%Y%m%dT%H%M%S").to_string(),
    );
}