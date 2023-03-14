use cli_lib::export_schema_to;
use thir_export;

pub fn export_cli_schema_to(path: &thir_export::PathOrDash) {
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
    struct TypesEntrypoint {
        item: cli_lib::options::thir_elab_part::Options,
    }
    let schema = schemars::schema_for!(TypesEntrypoint);
    serde_json::to_writer(path.open_or_stdout(), &schema).unwrap();
}

fn main() {
    match std::env::args().collect::<Vec<_>>().as_slice() {
        [_, kind, destination] if kind == "cli" || kind == "ast" => {
            let destination = thir_export::PathOrDash::from(std::ffi::OsStr::new(destination));
            if kind == "cli" {
                export_cli_schema_to(&destination)
            } else {
                export_schema_to::export_schema_to(&destination)
            }
        }
        [bin, _rest @ ..] => {
            eprintln!("Usage: {} (ast|cli) OUTPUT_FILE", bin);
            std::process::exit(1)
        }
        _ => panic!(),
    }
}
