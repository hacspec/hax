use clap::Parser;
use colored::Colorize;
use hax_cli_options::{NormalizePaths, Options};
use std::process::Command;

/// Return a toolchain argument to pass to [cargo]: when the correct nightly is
/// already present, this is None, otherwise we (1) ensure [rustup] is available
/// (2) install the nightly (3) return the toolchain
fn toolchain() -> Option<&'static str> {
    let current_rustc_version = version_check::triple()
        .map(|(_, channel, date)| format!("{channel}-{date}"))
        .unwrap_or("unknown".into());
    if env!("HAX_RUSTC_VERSION") != current_rustc_version {
        const TOOLCHAIN: &str = env!("HAX_TOOLCHAIN");
        // ensure rustup is available
        which::which("rustup").ok().unwrap_or_else(|| {
            println!("Error: {} was not found, but toolchain {} is required while the current toolchain is {}\n\nExiting.", "rustup".bold(), TOOLCHAIN.bold(), current_rustc_version.bold());
            std::process::exit(1)
        });
        // make sure the toolchain is installed
        rustup_toolchain::install(TOOLCHAIN).unwrap();
        // return the correct toolchain
        Some(TOOLCHAIN)
    } else {
        None
    }
}

/// [get_args] is a wrapper of `std::env::args` that strips a possible
/// cargo subcommand. This allows for a binary [BINARY] to be called
/// both with [cargo BINARY args...] and [cargo-BINARY args...].
// pub fn get_args(subcommand: &str) -> Vec<String> {
pub fn get_args(subcommand: &str) -> impl Iterator<Item = String> {
    let mut args = std::env::args().peekable();
    // `current_binary` is expected to be something like `cargo` or `cargo-hax`
    let current_binary = args.next().unwrap();
    // strip the subcommand `hax` if we see it
    args.next_if_eq(&subcommand.to_string());
    // put back `current_binary` in front
    [current_binary].into_iter().chain(args)
}

/// Our custom rustc driver will *not* be run in an proper terminal,
/// thus logs would appear uncolored. When no RUST_LOG_STYLE env. var.
/// is set, [rust_log_style] checks wether the [cargo hax] command was
/// run inside a terminal. If it was inside a terminal,
/// [rust_log_style] returns ["always"], which is the usual default
/// behavior. Otherwise we return ["never"]. When [RUST_LOG_STYLE] is
/// set, we just return its value.
fn rust_log_style() -> String {
    std::env::var("RUST_LOG_STYLE").unwrap_or_else(|_| {
        use is_terminal::IsTerminal;
        if std::io::stderr().is_terminal() {
            "always".to_string()
        } else {
            "never".to_string()
        }
    })
}

/// Helpers to resolve (at runtime) the location of the Hax Engine.
/// If no hax engine can be found installed, `resolve_path` will
/// attempt (after user confirmation) at downloading a prebuilt JS
/// dist (`download_compatible_prebuilt_js_hax_engine`).
mod resolve_engine {
    use colored::Colorize;
    use const_format::formatcp;
    use hax_cli_options::{HaxEnginePath, Options, RUST_SRC_HASH};
    use std::path::{Path, PathBuf};

    /// Default binary name expected in PATH
    const ENGINE_BINARY_NAME: &str = "hax-engine";
    /// Expected name in case of a JS Hax Engine
    const ENGINE_JS_FILENAME: &str = formatcp!("{}.js", RUST_SRC_HASH);
    /// From where should the dists be downloaded from
    const DISTS_ROOT_URI: &str = "https://hacspec.org/hax-engine-dists/dists";
    const DIST_URI: &str = formatcp!("{}/{}", DISTS_ROOT_URI, ENGINE_JS_FILENAME);
    const ENGINE_BINARY_NOT_FOUND: &str = formatcp!(
        "The binary [{}] was not found in your [PATH].",
        ENGINE_BINARY_NAME,
    );

    /// Compute the location where to (possibly) put a JS downloaded
    /// version of the Hax engine.
    fn js_engine_path() -> Option<PathBuf> {
        let cache_dir = dirs::cache_dir()?.join("hax");
        let js_engine_path = cache_dir.clone().join(ENGINE_JS_FILENAME);
        Some(js_engine_path)
    }

    /// Tries to download a prebuild Hax Engine at `DIST_URI`.
    fn download_compatible_prebuilt_js_hax_engine(target_path: &Path) {
        let resp = reqwest::blocking::get(DIST_URI).unwrap();
        if !resp.status().is_success() {
            eprintln!("\n{}\n", format!("Could not download a compatible Hax Engine: tried to download {}, but the request wasn't successful (got {}).", DIST_URI.bold(), resp.status().to_string().bold()).red());
            panic!()
        }
        std::fs::create_dir_all(target_path.parent().unwrap()).unwrap();
        std::fs::write(target_path, resp.bytes().unwrap()).unwrap();
        eprintln!(
            "Downloaded Hax Engine from {} to file {} successfully.",
            DIST_URI.bold(),
            target_path.display().to_string().bold()
        );
    }

    /// Dynamically looks for the Hax Engine.
    ///  1. Use the environment variable `HAX_ENGINE_BINARY` if set.
    ///  2. Use binary located at `ENGINE_BINARY_NAME` if exists in PATH.
    ///  3. Use javascript script located at `js_engine_path()` (if that file exists).
    ///  4. Try to fetch that javascript script from the internet otherwise.
    ///     (note: this asks interactively the user first)
    fn resolve_path() -> HaxEnginePath {
        use which::which;
        use HaxEnginePath::*;

        std::env::var("HAX_ENGINE_BINARY")
            .ok()
            .map(|name| Native(PathBuf::from(name)))
            .or_else(|| which(ENGINE_BINARY_NAME).ok().map(Native))
            .or_else(|| {
                const ERR: &str =
                    "Could not find a place where to store `hax-engine.js`. `dirs::cache_dir()`";
                let js_engine_path = js_engine_path().expect(ERR);
                if js_engine_path.is_file() {
                    return Some(NodeJs(js_engine_path));
                }
                let q = &format!(
                    "{} Should I try to download a prebuilt Hax Engine from {}?",
                    ENGINE_BINARY_NOT_FOUND,
                    DISTS_ROOT_URI.bold(),
                );
                (inquire::Confirm::new(q).with_default(true).prompt().ok() == Some(true)).then(
                    || {
                        if which("node").is_err() {
                            panic!("Please install NodeJS: the prebuilt engine uses JavaScript.")
                        }
                        download_compatible_prebuilt_js_hax_engine(&js_engine_path);
                        NodeJs(js_engine_path)
                    },
                )
            })
            .expect(&ENGINE_BINARY_NOT_FOUND)
    }

    /// Whenever the backend `hax_engine_path` option is set to
    /// `AutoDetect`, resolves the engine and substitutes `AutoDetect`
    /// with a concrete path to Hax Engine.
    pub fn options(options: &mut Options) {
        use hax_cli_options::*;
        if let Some(Command::ExporterCommand(ExporterCommand::Backend(BackendOptions {
            hax_engine_path: opts @ HaxEnginePath::AutoDetect,
            ..
        }))) = &mut options.command
        {
            *opts = resolve_path();
        }
    }
}

fn main() {
    let options = {
        let mut options = Options::parse_from(get_args("hax"));
        options.normalize_paths(); // take care of relative paths
        resolve_engine::options(&mut options); // take care of hax engine path
        options
    };

    let child = Command::new("cargo")
        .args(["build".into()].iter().chain(options.cargo_flags.iter()))
        .envs(
            toolchain()
                .map(|t| vec![("RUSTUP_TOOLCHAIN", t)])
                .unwrap_or(vec![]),
        )
        .env(
            "RUSTC_WORKSPACE_WRAPPER",
            std::env::var("HAX_RUSTC_DRIVER_BINARY")
                .unwrap_or("driver-hax-frontend-exporter".into()),
        )
        .env("RUST_LOG_STYLE", rust_log_style())
        .env(
            hax_cli_options::ENV_VAR_OPTIONS_FRONTEND,
            serde_json::to_string(&options)
                .expect("Options could not be converted to a JSON string"),
        )
        .spawn();

    std::process::exit(child.unwrap().wait().unwrap().code().unwrap_or(254))
}
