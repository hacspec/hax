pub mod options;

use circus_frontend;
use std::process::Command;

pub fn export_schema_to(path: &circus_frontend::PathOrDash) {
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
    struct TypesEntrypoint {
        item: circus_frontend::Item,
    }
    let schema = schemars::schema_for!(TypesEntrypoint);
    serde_json::to_writer(path.open_or_stdout(), &schema).unwrap();
}

pub fn get_args(subcommand: &str) -> Vec<String> {
    let mut args: Vec<_> = std::env::args().collect();
    if args.get(1) == Some(&subcommand.to_string()) {
        // we face a call `cargo [subcommand]`: we need to get rid of the first argument
        args = args.into_iter().skip(1).collect();
    }
    args
}

pub fn run(options: circus_frontend::Options) -> i32 {
    options.export_json_schema.as_ref().map(export_schema_to);

    let exit_status = Command::new("cargo")
        .args(["build".into()].iter().chain(options.cargo_flags.iter()))
        .env("RUSTC_WORKSPACE_WRAPPER", "driver-circus-frontend")
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
