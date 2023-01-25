#![feature(iter_intersperse)]

use std::process::Command;

fn main() {
    let args: Vec<_> = std::env::args().skip(2).collect();
    let cargo_args = args
        .iter()
        .skip_while(|arg| *arg != "--")
        .skip_while(|arg| *arg == "--");

    let thir_export_args = args
        .iter()
        .take_while(|arg| *arg != "--")
        .map(|x| escape_string::escape(&x).into())
        .intersperse(" ".to_string())
        .collect::<String>();

    let exit_status = Command::new("cargo")
        .args(["build".into()].iter().chain(cargo_args))
        // TODO: without setting CARGO_CACHE_RUSTC_INFO, cargo seems
        // just to cache its call to the custom driver.
        // Clearly, that seems hacky.
        .env("CARGO_CACHE_RUSTC_INFO", "1")
        .env("RUSTC_WORKSPACE_WRAPPER", "driver-thir-export")
        .env("THIR_EXPORT_ARGS", thir_export_args)
        .spawn()
        .unwrap()
        .wait()
        .unwrap();

    std::process::exit(exit_status.code().unwrap_or(-1));
}
