pub fn writer_of_path(path: &String) -> Box<dyn std::io::Write> {
    if path == "-" {
        box std::io::stdout()
    } else {
        box std::fs::File::create(&path).unwrap()
    }
}

pub fn export_schema_to(path: &String) {
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
    struct TypesEntrypoint {
        item: crate::Item,
    }
    let schema = schemars::schema_for!(TypesEntrypoint);
    serde_json::to_writer(writer_of_path(path), &schema).unwrap();
}
