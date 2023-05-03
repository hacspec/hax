use std::process::Command;

use regex::Regex;

pub struct Test {
    pub stderr: &'static str,
    pub manifest_path: &'static str,
}

/// We need to install the driver before we can run the circus command.
/// "cargo install --path cli/driver"
pub fn install_driver() {
    let mut cmd = Command::new("cargo");
    cmd.current_dir("../../");

    let status = cmd
        .args(&["install", "--path", "cli/driver"])
        .output()
        .unwrap()
        .status;
    assert!(status.success());
}

pub const REGEX_STRING: &str = r"(?m)^(\s*[Blocking|Running|Finished|Compiling][\S]+.*\n*)";

pub fn filter_stderr(stderr: &[u8]) -> String {
    let err_str = String::from_utf8_lossy(stderr);

    let re = Regex::new(REGEX_STRING).unwrap();
    assert!(re.is_match(&err_str));

    eprintln!("stderr:\n{err_str}");
    let err_str = re.replace_all(&err_str, "");
    let err_str = err_str.trim();
    eprintln!("stderr:\n{err_str}");

    err_str.to_string()
}
