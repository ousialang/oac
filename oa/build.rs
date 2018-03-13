use std::process::Command;

fn main() {
    set_env_var("CARGO_PKG_HASH", git_commit_hash());
    set_env_var("CARGO_PKG_TAGS", String::new());
}

fn set_env_var(key: &str, value: String) {
    println!("cargo:rustc-env={}={}", key, value);
}

fn git_commit_hash() -> String {
    match Command::new("git").args(&["rev-parse", "HEAD"]).output() {
        Ok(o) => {
            String::from_utf8(o.stdout)
                .expect("encoding error while reading 'git' output")
                .chars()
                .take(8)
                .collect()
        }
        Err(_) => "????????".to_owned(),
    }
}
