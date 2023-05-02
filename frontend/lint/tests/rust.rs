//! Tests for the Rust linter

use std::process::Command;

use regex::Regex;

struct Test {
    stderr: &'static str,
    manifest_path: &'static str,
}

const TESTS: [Test; 2] = [
    Test {
        stderr: "warning: [Circus] FnMut is not supported
 --> fnmut/src/lib.rs:8:12
  |
8 |         F: FnMut(u32) -> u8;
  |            ^^^^^

warning: [Circus] FnMut is not supported
  --> fnmut/src/lib.rs:16:12
   |
16 |         F: FnMut(u32) -> u8,
   |            ^^^^^

warning: `fnmut` (lib) generated 2 warnings",
        manifest_path: "lint/rust_tests/fnmut/Cargo.toml",
    },
    Test {
        stderr: "warning: [Circus] FnMut is not supported
 --> fnmut/src/lib.rs:8:12
  |
8 |         F: FnMut(u32) -> u8;
  |            ^^^^^

warning: [Circus] FnMut is not supported
  --> fnmut/src/lib.rs:16:12
   |
16 |         F: FnMut(u32) -> u8,
   |            ^^^^^

warning: `fnmut` (lib) generated 2 warnings",
        manifest_path: "lint/rust_tests/fnmut/Cargo.toml",
    },
];

#[test]
fn run() {
    for test in TESTS {
        let mut cmd = Command::new("cargo");
        cmd.current_dir("../");

        let output = cmd
            .args(&[
                "run",
                "--bin",
                "cargo-circus",
                "--",
                "-C",
                "--manifest-path",
                test.manifest_path,
            ])
            .output()
            .unwrap();
        eprintln!("{:?}", output);

        let err_str = String::from_utf8_lossy(&output.stderr);

        let re = Regex::new(r"(?m)^(\s*[Blocking|Running|Finished|Compiling][\S]+.*\n*)").unwrap();
        assert!(re.is_match(&err_str));

        eprintln!("stderr:\n{err_str}");
        let err_str = re.replace_all(&err_str, "");
        let err_str = err_str.trim();
        eprintln!("stderr:\n{err_str}");

        assert_eq!(err_str, test.stderr);
    }
}
