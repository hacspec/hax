use hax_cli_options::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

type ThirBody = hax_frontend_exporter::ThirBody;

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct EngineOptions {
    pub backend: BackendOptions,
    pub input: Vec<hax_frontend_exporter::Item<ThirBody>>,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct File {
    pub path: String,
    pub contents: String,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct Output {
    pub diagnostics: Vec<hax_diagnostics::Diagnostics<Vec<hax_frontend_exporter::Span>>>,
    pub files: Vec<File>,
    pub debug_json: Option<String>,
}
