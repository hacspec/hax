mod common;

use clap::Parser;
use std::process::Command;

fn main() {
    let args = common::get_args("circus");

    let opts = common::options::circus_engine_part::Options::parse_from(args.iter());

    let output_file = tempfile::NamedTempFile::new().unwrap();
    let path = output_file.path().to_path_buf();

    let exit_status = common::run(
        (common::options::circus_frontend_part::All {
            extra: common::options::circus_frontend_part::Extra {
                export_json_schema: None,
                output_file: circus_frontend::PathOrDash::Path(path.clone()),
            },
            base: opts.circus_frontend.clone(),
            force_cargo_build: opts.force_cargo_build.clone(),
        })
        .into(),
    );
    if exit_status != 0 {
        std::process::exit(exit_status);
    }

    let exit_status = Command::new("circus-engine")
        .env("CIRCUS_ENGINE_INPUT", path)
        .env(
            "CIRCUS_ENGINE_OPTIONS",
            serde_json::to_string(&opts).expect("Options could not be converted to a JSON string"),
        )
        .spawn()
        .map_err(|e| {
            if let std::io::ErrorKind::NotFound = e.kind() {
                panic!("The binary [circus-engine] was not found in your [PATH].")
            }
            e
        })
        .unwrap()
        .wait()
        .unwrap();

    output_file.close().unwrap();
    std::process::exit(exit_status.code().unwrap_or(-1));
}
