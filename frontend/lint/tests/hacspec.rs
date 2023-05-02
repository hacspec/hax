//! Tests for the hacspec linter

use std::process::Command;

use regex::Regex;

struct Test {
    stderr: &'static str,
    manifest_path: &'static str,
}

const TESTS: [Test; 2] = [
    Test {
        stderr: "",
        manifest_path: "lint/hacspec_tests/v1-lib/Cargo.toml",
    },
    Test {
        stderr: "warning: [Circus] Mutable arguments are not supported
 --> mut_arg/src/lib.rs:1:23
  |
1 | pub fn add(left: &mut usize, right: usize) {
  |                       ^^^^^

warning: `mut_arg` (lib) generated 1 warning",
        manifest_path: "lint/hacspec_tests/mut_arg/Cargo.toml",
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
                ";",
                "lint",
                "hacspec",
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
