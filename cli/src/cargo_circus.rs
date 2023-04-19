mod common;

use circus_cli_options::Options;
use clap::Parser;
use std::process::Command;

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

fn main() {
    let args = common::get_args("circus");
    let options = Options::parse_from(args.iter());

    std::process::exit(
        cargo_command()
            .args(["build".into()].iter().chain(options.cargo_flags.iter()))
            .env("RUSTC_WORKSPACE_WRAPPER", "driver-circus-frontend-exporter")
            .env(
                circus_cli_options::ENV_VAR_OPTIONS_FRONTEND,
                serde_json::to_string(&options)
                    .expect("Options could not be converted to a JSON string"),
            )
            .spawn()
            .unwrap()
            .wait()
            .unwrap()
            .code()
            .unwrap_or(254),
    )
}
