use lazy_static::{__Deref, lazy_static};
use std::{ffi::OsStr, process::Command};

pub trait CommandCircusExt {
    fn circus<I: IntoIterator<Item = S>, S: AsRef<OsStr>>(args: I) -> Self;
}

impl CommandCircusExt for Command {
    fn circus<I: IntoIterator<Item = S>, S: AsRef<OsStr>>(args: I) -> Command {
        use assert_cmd::cargo::cargo_bin;
        use std::path::PathBuf;
        struct Paths {
            driver: PathBuf,
            engine: PathBuf,
            cargo_circus: PathBuf,
        }
        const CARGO_CIRCUS: &str = "cargo-circus";
        lazy_static! {
            static ref PATHS: Option<Paths> = {
                if let "yes" | "y" | "true" | "1" = std::env::var("CARGO_TESTS_ASSUME_BUILT").unwrap_or("".into()).to_lowercase().as_str() {
                    return None;
                }
                let root = std::env::current_dir().unwrap();
                let root = root.parent().unwrap();
                let engine_dir = root.join("engine");
                // Make sure binaries are built
                assert!(Command::new("cargo")
                        .args(&["build", "--workspace", "--bins"])
                        .status()
                        .unwrap()
                        .success());
                assert!(Command::new("dune")
                        .args(&["build"])
                        .env("CIRCUS_JSON_SCHEMA_EXPORTER_BINARY", cargo_bin("circus-export-json-schemas"))
                        .current_dir(engine_dir.clone())
                        .status()
                        .unwrap()
                        .success());
                Some(Paths {
                    driver: cargo_bin("driver-circus-frontend-exporter"),
                    cargo_circus: cargo_bin(CARGO_CIRCUS),
                    engine: engine_dir.join("_build/install/default/bin/circus-engine"),
                })
            };
        }
        let mut cmd = match PATHS.deref() {
            Some(paths) => {
                let mut cmd = Command::new(paths.cargo_circus.clone());
                cmd.env("CIRCUS_RUSTC_DRIVER_BINARY", paths.driver.clone());
                cmd.env("CIRCUS_ENGINE_BINARY", paths.engine.clone());
                cmd
            }
            None => Command::new(CARGO_CIRCUS),
        };
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
