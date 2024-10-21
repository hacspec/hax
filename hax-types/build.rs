macro_rules! set_empty_env_var_with {
    ($var:literal, $f: expr) => {{
        println!("cargo:rurun-if-env-changed={}", $var);
        match option_env!($var) {
            Some(value) => value.to_string(),
            None => {
                let value = $f;
                println!("cargo:rustc-env={}={}", $var, value);
                value
            }
        }
    }};
}

const UNKNOWN: &str = "unknown";

fn git_command(args: &[&str]) -> String {
    std::process::Command::new("git")
        .args(args)
        .output()
        .map(|output| String::from_utf8(output.stdout).unwrap().trim().to_string())
        .ok()
        .filter(|s| !s.is_empty())
        .unwrap_or(UNKNOWN.to_string())
}

fn main() {
    let commit_hash =
        set_empty_env_var_with!("HAX_GIT_COMMIT_HASH", git_command(&["rev-parse", "HEAD"]));

    set_empty_env_var_with!("HAX_VERSION", {
        if commit_hash == UNKNOWN {
            env!("CARGO_PKG_VERSION").into()
        } else {
            git_command(&["tag", "--contains", &commit_hash])
                .lines()
                .next()
                .and_then(|tag| tag.split_once("hax-v"))
                .map(|(_, version)| version.trim().to_string())
                .unwrap_or_else(|| format!("untagged-git-rev-{}", &commit_hash[0..10]))
        }
    });
}
