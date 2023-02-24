#![feature(iter_intersperse)]

use clap::Parser;
use std::process::Command;
use thir_export;

fn main() {
    let args: Vec<_> = {
        let mut args: Vec<_> = std::env::args().collect();
        if std::path::PathBuf::from(args[0].clone()) == std::env::current_exe().unwrap() {
            args = args.into_iter().skip(1).collect();
        }
        args
    };

    let options = thir_export::Options::parse_from(args.iter());

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

    std::process::exit(exit_status.code().unwrap_or(-1));
}
