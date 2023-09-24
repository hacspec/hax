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

/// The Rust frontend of Hax defines all the datatypes, and we send
/// JSON to the engine that conform to those datatypes. Thus, to be
/// compatible with the Hax frontend, the Hax engine should expect
/// exactly the correct types. `hash_of_sources` computes a hash that
/// captures all the Rust source of the frontend.
fn hash_of_sources() -> String {
    use sha2::{Digest, Sha256};
    use std::ffi::OsStr;
    use std::path::{Path, PathBuf};
    use std::{fs, io};

    const ROOT: &str = "../..";
    let denylist: Vec<_> = {
        [
            "target",
            "engine",
            "tests",
            "test-harness",
            "hax-lib-macros",
        ]
        .iter()
        .map(|s| format!("{}/{}", ROOT, s))
        .map(PathBuf::from)
        .collect()
    };
    fn visit<P: AsRef<Path>>(path: P, denylist: &Vec<PathBuf>) -> Vec<PathBuf> {
        fs::read_dir(path)
            .unwrap()
            .flat_map(|item| {
                let item = item.unwrap();
                let path = item.path();
                if item.metadata().unwrap().is_dir() && !denylist.contains(&path) {
                    visit(path, denylist)
                } else if path.extension() == Some(OsStr::new("rs")) {
                    vec![path]
                } else {
                    vec![]
                }
            })
            .collect()
    }

    let mut hasher = Sha256::new();
    let mut paths = visit(ROOT, &denylist);
    paths.sort();
    for path in &paths {
        println!("cargo:rerun-if-changed={}", path.display());
        let mut file = fs::File::open(path.clone()).unwrap();
        io::copy(&mut file, &mut hasher).unwrap();
    }
    let hash_bytes = hasher.finalize();
    format!("{:#x}", hash_bytes)
}

/// Produces the HAX_RUST_SRC_HASH environment variable.
fn hash_of_sources_env_var() {
    println!("cargo:rustc-env=HAX_RUST_SRC_HASH={}", hash_of_sources());
}

fn main() {
    set_empty_env_var_with_git!(
        "HAX_GIT_DESCRIBE",
        ["describe", "--tags", "--always", "--abbrev=0"]
    );
    set_empty_env_var_with_git!("HAX_GIT_COMMIT_HASH", ["rev-parse", "HEAD"]);
    hash_of_sources_env_var();
}
