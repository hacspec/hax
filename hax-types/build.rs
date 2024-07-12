macro_rules! set_empty_env_var_with_git {
    ($var:literal, $args: expr) => {
        if let None = option_env!($var) {
            println!(
                "cargo:rustc-env={}={}",
                $var,
                std::process::Command::new("git")
                    .args($args)
                    .output()
                    .map(|output| String::from_utf8(output.stdout).unwrap())
                    .unwrap_or("unknown".into())
            );
        }
        println!("cargo:rurun-if-env-changed={}", $var);
    };
}

fn main() {
    set_empty_env_var_with_git!(
        "HAX_GIT_DESCRIBE",
        ["describe", "--tags", "--always", "--abbrev=0"]
    );
    set_empty_env_var_with_git!("HAX_GIT_COMMIT_HASH", ["rev-parse", "HEAD"]);
}
