#![feature(iter_intersperse)]

use clap::Parser;
use std::process::Command;
use thir_export;
mod export_schema_to;

fn absolute_path(path: impl AsRef<std::path::Path>) -> std::io::Result<std::path::PathBuf> {
    use path_clean::PathClean;
    let path = path.as_ref();

    let absolute_path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()?.join(path)
    }
    .clean();

    Ok(absolute_path)
}

fn main() {
    let args: Vec<_> = {
        let mut args: Vec<_> = std::env::args().collect();
        if std::path::PathBuf::from(args[0].clone()) == std::env::current_exe().unwrap() {
            args = args.into_iter().skip(1).collect();
        }
        args
    };

    let mut options = thir_export::Options::parse_from(args.iter());

    // Make path absolute: the options are passed to [cargo build]
    // command below, which might change the current working dir.
    options.output_file = options.output_file.map_path(|p| absolute_path(p).unwrap());
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

    std::process::exit(exit_status.code().unwrap_or(-1));
}
