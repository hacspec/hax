#![feature(iter_intersperse)]

use clap::Parser;
use serde::Serialize;
use std::process::Command;
use thir_export;

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let cargo_args = args
        .iter()
        .skip_while(|arg| *arg != "--")
        .skip_while(|arg| *arg == "--");

    let options = thir_export::Options::parse_from(args.iter().take_while(|arg| *arg != "--"));

    let exit_status = Command::new("cargo")
        .args(["build".into()].iter().chain(cargo_args))
        // TODO: without setting CARGO_CACHE_RUSTC_INFO, cargo seems
        // just to cache its call to the custom driver.
        // Clearly, that seems hacky.
        .env("CARGO_CACHE_RUSTC_INFO", "1")
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
