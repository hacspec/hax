mod common;

use circus_frontend;

pub fn export_cli_schema_to(path: &circus_frontend::PathOrDash) {
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
    struct TypesEntrypoint {
        item: common::options::circus_engine_part::Options,
    }
    let schema = schemars::schema_for!(TypesEntrypoint);
    serde_json::to_writer(path.open_or_stdout(), &schema).unwrap();
}

fn main() {
    match std::env::args().collect::<Vec<_>>().as_slice() {
        [_, kind, destination] if kind == "cli" || kind == "ast" => {
            let destination = circus_frontend::PathOrDash::from(std::ffi::OsStr::new(destination));
            if kind == "cli" {
                export_cli_schema_to(&destination)
            } else {
                common::export_schema_to(&destination)
            }
        }
        [bin, _rest @ ..] => {
            eprintln!("Usage: {} (ast|cli) OUTPUT_FILE", bin);
            std::process::exit(1)
        }
        _ => panic!(),
    }
}
