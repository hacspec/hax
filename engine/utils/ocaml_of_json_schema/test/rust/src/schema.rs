mod lib;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize, PartialEq)]
struct Wrapper {
    typ: lib::Test,
}

fn main() {
    let schema = schemars::schema_for!(Wrapper);
    println!("{}", serde_json::to_string(&schema).unwrap());
}
