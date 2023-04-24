use circus_cli_options::Options;
use clap::Parser;
use std::{
    io::{self, Write},
    process::Command,
};

/// Return a [Command] for [cargo]: when the correct nightly is
/// already present, this is just the command [cargo], otherwise we
/// (1) ensure [rustup] is available (2) install the nightly (3) tell
/// cargo to the nightly
fn cargo_command() -> Command {
    let (_version, channel, date) = version_check::triple().unwrap();
    let current_rustc_version = format!("{channel}-{date}");
    let mut cmd = Command::new("cargo");
    if env!("CIRCUS_RUSTC_VERSION") != current_rustc_version {
        const TOOLCHAIN: &str = env!("CIRCUS_TOOLCHAIN");
        // ensure rustup is available
        which::which("rustup").expect(&format!("rustup was not found, but toolchain {TOOLCHAIN} is required while the current toolchain is {current_rustc_version}"));
        // make sure the toolchain is installed
        rustup_toolchain::install(TOOLCHAIN).unwrap();
        // add a [rustup] flag to cargo
        cmd.arg(format!("+{TOOLCHAIN}"));
    }
    cmd
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
    let args: Vec<String> = get_args("circus");
    let options = Options::parse_from(args.iter());

    let child = cargo_command()
        .args(["build".into()].iter().chain(options.cargo_flags.iter()))
        .env("RUSTC_WORKSPACE_WRAPPER", "driver-circus-frontend-exporter")
        .env(
            circus_cli_options::ENV_VAR_OPTIONS_FRONTEND,
            serde_json::to_string(&options)
                .expect("Options could not be converted to a JSON string"),
        )
        .spawn()
        .unwrap();
    let output = child.wait_with_output().unwrap();
    io::stdout().write_all(&output.stdout).unwrap();
    io::stderr().write_all(&output.stderr).unwrap();
    std::process::exit(output.status.code().unwrap_or(254))
}
