//! Tests for the Rust linter

use std::process::Command;

mod util;
use util::*;

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
    install_driver();

    for test in TESTS {
        let mut cmd = Command::new("cargo");
        cmd.current_dir("../");

        let cmd = cmd.args(&[
            "run",
            "--bin",
            "cargo-circus",
            "--",
            "-C",
            "--manifest-path",
            test.manifest_path,
        ]);

        let output = cmd.output().unwrap();
        eprintln!("{:?}", output);
        let output = cmd.output().unwrap();
        eprintln!("{:?}", output);

        let err_str = filter_stderr(&output.stderr);
        assert_eq!(err_str, test.stderr);
    }
}
