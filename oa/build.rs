extern crate chrono;

use std::process::Command;

use chrono::Utc;


fn main() {
    set_rustc_var("CARGO_PKG_HASH", git_commit_hash());
    set_rustc_var("CARGO_PKG_TIMESTAMP_RFC3339", Utc::now().to_rfc3339());
}


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
