use hax_cli_options::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

type ThirBody = hax_frontend_exporter::ThirBody;

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct EngineOptions {
    pub backend: BackendOptions,
    pub input: Vec<hax_frontend_exporter::Item<ThirBody>>,
    pub manifest_dir: String,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
}

#[allow(non_snake_case)]
#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct SourceMap {
    pub mappings: String,
    pub sourceRoot: String,
    pub sources: Vec<String>,
    pub sourcesContent: Vec<Option<String>>,
    pub names: Vec<String>,
    pub version: u8,
    pub file: String,
}

impl SourceMap {
    pub fn inline_sources_content(&mut self) {
        self.sourcesContent = vec![];
        for source in &self.sources {
            let path = if self.sourceRoot.is_empty() {
                source.clone()
            } else {
                format!("{}/{}", &self.sourceRoot, source)
            };
            eprintln!("path={path}");
            let contents = Some(std::fs::read_to_string(path).unwrap());
            self.sourcesContent.push(contents);
        }
    }
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct File {
    pub path: String,
    pub contents: String,
    pub sourcemap: Option<SourceMap>,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct Output {
    pub diagnostics: Vec<hax_diagnostics::Diagnostics<Vec<hax_frontend_exporter::Span>>>,
    pub files: Vec<File>,
    pub debug_json: Option<String>,
}

// This is located here for dependency reason, but this is not related
// to the engine (yet?).
#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct WithDefIds<Body: hax_frontend_exporter::IsBody> {
    pub def_ids: Vec<hax_frontend_exporter::DefId>,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    pub items: Vec<hax_frontend_exporter::Item<Body>>,
}
