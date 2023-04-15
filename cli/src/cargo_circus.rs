mod common;

use clap::Parser;
use common::options::{circus_engine_part, wrapped};
use std::process::Command;

fn main() {
    let args = common::get_args("circus");

    let opts = wrapped::Options::parse_from(args.iter());

    let (engine_data, output_file_path) = match opts.backend {
        wrapped::JsonOrBackend::JSON { output_file } => (None, output_file),
        wrapped::JsonOrBackend::Backend(backend) => {
            let file = tempfile::NamedTempFile::new().unwrap();
            let path = file.path().to_path_buf();
            (
                Some((
                    file,
                    circus_engine_part::Options {
                        backend,
                        circus_frontend_exporter: opts.circus_frontend_exporter.clone(),
                        output_dir: opts.output_dir,
                    },
                    path.clone(),
                )),
                circus_frontend_exporter::PathOrDash::Path(path),
            )
        }
    };

    let exit_status = common::run(
        (common::options::circus_frontend_part::All {
            extra: common::options::circus_frontend_part::Extra {
                export_json_schema: None,
                output_file: output_file_path,
            },
            base: opts.circus_frontend_exporter.clone(),
            force_cargo_build: opts.force_cargo_build.clone(),
        })
        .into(),
    );
    if exit_status != 0 {
        std::process::exit(exit_status);
    }

    if let Some((output_file, opts, path)) = engine_data {
        let exit_status = Command::new("circus-engine")
            .env("CIRCUS_ENGINE_INPUT", path)
            .env(
                "CIRCUS_ENGINE_OPTIONS",
                serde_json::to_string(&opts)
                    .expect("Options could not be converted to a JSON string"),
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
}
