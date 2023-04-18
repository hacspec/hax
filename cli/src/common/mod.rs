// pub mod options;

// use circus_frontend_exporter;
// use std::process::Command;

// pub fn export_schema_to(path: &circus_frontend_exporter::PathOrDash) {
//     use schemars::JsonSchema;
//     use serde::{Deserialize, Serialize};
//     #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
//     struct TypesEntrypoint {
//         item: circus_frontend_exporter::Item,
//     }
//     let schema = schemars::schema_for!(TypesEntrypoint);
//     serde_json::to_writer(path.open_or_stdout(), &schema).unwrap();
// }

pub fn get_args(subcommand: &str) -> Vec<String> {
    let mut args: Vec<_> = std::env::args().collect();
    if args.get(1) == Some(&subcommand.to_string()) {
        // we face a call `cargo [subcommand]`: we need to get rid of the first argument
        args = args.into_iter().skip(1).collect();
    }
    args
}
