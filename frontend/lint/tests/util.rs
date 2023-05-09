use lazy_static::lazy_static;
use std::{ffi::OsStr, process::Command};

use regex::Regex;

pub struct Test {
    pub stderr: &'static str,
    pub manifest_path: &'static str,
}

pub trait CommandCircusExt {
    fn circus<I: IntoIterator<Item = S>, S: AsRef<OsStr>>(args: I) -> Self;
}

impl CommandCircusExt for Command {
    fn circus<I: IntoIterator<Item = S>, S: AsRef<OsStr>>(args: I) -> Command {
        use assert_cmd::cargo::cargo_bin;
        use std::path::PathBuf;
        struct Paths {
            driver: PathBuf,
            cargo_circus: PathBuf,
        }
        lazy_static! {
            static ref PATHS: Paths = {
                // Make sure binaries are built
                assert!(Command::new("cargo")
                    .args(&["build", "--workspace", "--bins"])
                    .status()
                    .unwrap()
                    .success());
                Paths {
                    driver: cargo_bin("driver-circus-frontend-exporter"),
                    cargo_circus: cargo_bin("cargo-circus"),
                }
            };
        }
        let mut cmd = Command::new(PATHS.cargo_circus.clone());
        cmd.env("CIRCUS_RUSTC_DRIVER_BINARY", PATHS.driver.clone());
        cmd.args(args);
        // As documented in
        // https://doc.rust-lang.org/cargo/reference/environment-variables.html#dynamic-library-paths,
        // [cargo run] (and thus also [cargo test]) sets dynamic
        // library paths, which causes some issues with dependencies
        // when compiling without rustup
        for env in ["DYLD_FALLBACK_LIBRARY_PATH", "LD_LIBRARY_PATH"] {
            cmd.env_remove(env);
        }
        cmd
    }
}

pub const REGEX_STRING: &str = r"(?m)^(\s*[Blocking|Running|Finished|Compiling][\S]+.*\n*)";

pub fn filter_stderr(stderr: &[u8]) -> String {
    let err_str = String::from_utf8_lossy(stderr);

    let re = Regex::new(REGEX_STRING).unwrap();
    assert!(re.is_match(&err_str));

    eprintln!("stderr:\n{err_str}");
    let err_str = re.replace_all(&err_str, "");
    let err_str = err_str.trim();
    let err_str = err_str.replace("\\", "/"); // "Fix" paths on Windows.
    eprintln!("stderr:\n{err_str}");

    err_str
}
