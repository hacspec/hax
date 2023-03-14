pub mod export_schema_to;
pub mod options;

use std::process::Command;
use thir_export;

pub fn get_args(subcommand: &str) -> Vec<String> {
    let mut args: Vec<_> = std::env::args().collect();
    if args.get(1) == Some(&subcommand.to_string()) {
        // we face a call `cargo [subcommand]`: we need to get rid of the first argument
        args = args.into_iter().skip(1).collect();
    }
    args
}

pub fn run(options: thir_export::Options) -> i32 {
    options
        .export_json_schema
        .as_ref()
        .map(export_schema_to::export_schema_to);

    let exit_status = Command::new("cargo")
        .args(["build".into()].iter().chain(options.cargo_flags.iter()))
        .env("RUSTC_WORKSPACE_WRAPPER", "driver-thir-export")
        .env(
            "THIR_EXPORT_OPTIONS",
            serde_json::to_string(&options)
                .expect("Options could not be converted to a JSON string"),
        )
        .spawn()
        .unwrap()
        .wait()
        .unwrap();

    exit_status.code().unwrap_or(-1)
}
