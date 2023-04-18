mod common;

use circus_cli_options::{Command, Options};
use clap::Parser;

fn run(options: Options) -> i32 {
    let exit_status = std::process::Command::new("cargo")
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
        .unwrap();

    exit_status.code().unwrap_or(-1)
}

fn main() {
    // let engine_binary_path = find_circus_engine();

    let args = common::get_args("circus");
    let opts = Options::parse_from(args.iter());

    // let (engine_data, output_file_path) = match opts.clone().backend {
    //     Command::JSON { output_file } => (None, output_file),
    //     Command::Backend(backend) => {
    //         let file = tempfile::NamedTempFile::new().unwrap();
    //         let path = file.path().to_path_buf();
    //         (
    //             Some((file, backend, path.clone())),
    //             circus_cli_options::PathOrDash::Path(path),
    //         )
    //     }
    // };

    let exit_status = run(opts);
    if exit_status != 0 {
        std::process::exit(exit_status);
    }

    // if let Some((output_file, opts, path)) = engine_data {
    //     let exit_status = std::process::Command::new(engine_binary_path)
    //         .env("CIRCUS_ENGINE_INPUT", path)
    //         .env(
    //             "CIRCUS_ENGINE_OPTIONS",
    //             serde_json::to_string(&opts)
    //                 .expect("Options could not be converted to a JSON string"),
    //         )
    //         .spawn()
    //         .map_err(|e| {
    //             if let std::io::ErrorKind::NotFound = e.kind() {
    //                 panic!("The binary [circus-engine] was not found in your [PATH].")
    //             }
    //             e
    //         })
    //         .unwrap()
    //         .wait()
    //         .unwrap();
    //     output_file.close().unwrap();
    //     std::process::exit(exit_status.code().unwrap_or(-1));
    // }
}
