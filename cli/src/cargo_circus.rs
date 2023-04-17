mod common;

use clap::Parser;
use common::options::{circus_engine_part, wrapped};
use std::process::Command;

const ENGINE_BINARY_NAME: &str = "circus-engine";
const ENGINE_BINARY_NOT_FOUND: &str = const_format::formatcp!(
    "The binary [{}] was not found in your [PATH].",
    ENGINE_BINARY_NAME,
);

fn find_circus_engine() -> std::path::PathBuf {
    use which::which;

    which(ENGINE_BINARY_NAME)
        .ok()
        .or_else(|| {
            which("node").ok().and_then(|_| {
                if let Ok(true) = inquire::Confirm::new(&format!(
                    "{} Should I try to download it from GitHub?",
                    ENGINE_BINARY_NOT_FOUND,
                ))
                .with_default(true)
                .prompt()
                {
                    panic!("TODO: Downloading from GitHub is not supported yet.")
                } else {
                    None
                }
            })
        })
        .expect(&ENGINE_BINARY_NOT_FOUND)
}

fn main() {
    let engine_binary_path = find_circus_engine();

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
        let exit_status = Command::new(engine_binary_path)
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
