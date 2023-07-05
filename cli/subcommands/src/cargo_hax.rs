#![feature(type_changing_struct_update)]

use clap::Parser;
use colored::Colorize;
use hax_cli_options::{Command, NormalizePaths, Options, RustcCommand};

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
pub fn get_args(subcommand: &str) -> Vec<String> {
    let mut args: Vec<_> = std::env::args().collect();
    if args.get(1) == Some(&subcommand.to_string()) {
        // we face a call `cargo [subcommand]`: we need to get rid of the first argument
        args = args.into_iter().skip(1).collect();
    }
    args
}

fn main() {
    let args: Vec<String> = get_args("hax");
    let options: Options<Command> = Options::parse_from(args.iter()).normalize_paths();

    let mut cmd = std::process::Command::new("cargo");
    if let Some(toolchain) = toolchain() {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    cmd.arg("build").args(&options.cargo_flags);

    match options.command {
        Command::RustcCommand(command) => {
            let options: Options<RustcCommand> = Options { command, ..options };
            cmd.env(
                "RUSTC_WORKSPACE_WRAPPER",
                std::env::var("HAX_RUSTC_DRIVER_BINARY")
                    .unwrap_or("driver-hax-frontend-exporter".into()),
            );
            cmd.env(
                hax_cli_options::ENV_VAR_OPTIONS_FRONTEND,
                serde_json::to_string(&options)
                    .expect("Options could not be converted to a JSON string"),
            );
            std::process::exit(cmd.spawn().unwrap().wait().unwrap().code().unwrap_or(254))
        }
        Command::CheckCommand(backend) => {
            todo!()
        }
    }
}
