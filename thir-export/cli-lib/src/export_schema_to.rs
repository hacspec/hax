pub fn export_schema_to(path: &thir_export::PathOrDash) {
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
    struct TypesEntrypoint {
        item: thir_export::Item,
    }
    let schema = schemars::schema_for!(TypesEntrypoint);
    serde_json::to_writer(path.open_or_stdout(), &schema).unwrap();
}
