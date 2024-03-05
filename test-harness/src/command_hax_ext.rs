use lazy_static::{__Deref, lazy_static};
use std::{ffi::OsStr, process::Command};

pub trait CommandHaxExt {
    fn hax<I: IntoIterator<Item = S>, S: AsRef<OsStr>>(args: I) -> Self;
}

/// Computes a list of arguments that setup the number of parallel
/// jobs for dune accordingly to environment variable `DUNEJOBS`.
fn dune_jobs_args() -> Vec<String> {
    if let Ok(jobs) = std::env::var("DUNEJOBS") {
        vec!["-j".into(), jobs]
    } else {
        vec![]
    }
}

impl CommandHaxExt for Command {
    fn hax<I: IntoIterator<Item = S>, S: AsRef<OsStr>>(args: I) -> Command {
        use assert_cmd::cargo::cargo_bin;
        use std::path::PathBuf;
        struct Paths {
            driver: PathBuf,
            engine: PathBuf,
            cargo_hax: PathBuf,
        }
        const CARGO_HAX: &str = "cargo-hax";
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
                        .args(dune_jobs_args())
                        .env("HAX_JSON_SCHEMA_EXPORTER_BINARY", cargo_bin("hax-export-json-schemas"))
                        .env("HAX_ENGINE_NAMES_EXTRACT_BINARY", cargo_bin("hax-engine-names-extract"))
                        .current_dir(engine_dir.clone())
                        .status()
                        .unwrap()
                        .success());
                Some(Paths {
                    driver: cargo_bin("driver-hax-frontend-exporter"),
                    cargo_hax: cargo_bin(CARGO_HAX),
                    engine: engine_dir.join("_build/install/default/bin/hax-engine"),
                })
            };
        }
        let mut cmd = match PATHS.deref() {
            Some(paths) => {
                let mut cmd = Command::new(paths.cargo_hax.clone());
                cmd.env("HAX_RUSTC_DRIVER_BINARY", paths.driver.clone());
                cmd.env("HAX_ENGINE_BINARY", paths.engine.clone());
                cmd
            }
            None => Command::new(CARGO_HAX),
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
