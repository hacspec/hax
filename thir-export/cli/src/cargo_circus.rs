use clap::Parser;
use schemars::{schema_for, JsonSchema};
use serde::{Deserialize, Serialize};
use std::process::Command;
use thir_export;

use cli_lib::options;
// mod cargo_thir_export;
// use cargo_thir_export::run;

fn main() {
    let args = cli_lib::get_args("circus");

    let opts = options::thir_elab_part::Options::parse_from(args.iter());

    let output_file = tempfile::NamedTempFile::new().unwrap();
    let path = output_file.path().to_path_buf();

    let exit_status = cli_lib::run(
        (options::thir_export_part::All {
            extra: options::thir_export_part::Extra {
                export_json_schema: None,
                output_file: thir_export::PathOrDash::Path(path.clone()),
            },
            base: opts.thir_export.clone(),
            force_cargo_build: opts.force_cargo_build.clone(),
        })
        .into(),
    );
    if exit_status != 0 {
        std::process::exit(exit_status);
    }

    let exit_status = Command::new("thir-elab")
        .env("THIR_ELAB_INPUT", path)
        .env(
            "THIR_ELAB_OPTIONS",
            serde_json::to_string(&opts).expect("Options could not be converted to a JSON string"),
        )
        .spawn()
        .map_err(|e| {
            if let std::io::ErrorKind::NotFound = e.kind() {
                panic!("The binary [thir-elab] was not found in your [PATH].")
            }
            e
        })
        .unwrap()
        .wait()
        .unwrap();

    output_file.close().unwrap();
    std::process::exit(exit_status.code().unwrap_or(-1));
}
