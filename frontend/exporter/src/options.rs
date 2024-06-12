use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Glob {
    One,  // *
    Many, // **
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum NamespaceChunk {
    Glob(Glob),
    Exact(String),
}

impl std::convert::From<&str> for NamespaceChunk {
    fn from(s: &str) -> Self {
        match s {
            "*" => NamespaceChunk::Glob(Glob::One),
            "**" => NamespaceChunk::Glob(Glob::Many),
            _ => NamespaceChunk::Exact(String::from(s)),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct NamespacePattern {
    chunks: Vec<NamespaceChunk>,
}
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Namespace {
    /// A pattern that matches `DefId`s
    Pattern(NamespacePattern),
    /// An exact `DefId`
    Exact(crate::DefId),
}

impl std::convert::From<String> for Namespace {
    fn from(s: String) -> Self {
        if let Some(def_id) = crate::DefId::deserialize_compact(&s) {
            Self::Exact(def_id)
        } else {
            Self::Pattern(s.into())
        }
    }
}

impl std::convert::From<String> for NamespacePattern {
    fn from(s: String) -> Self {
        Self {
            chunks: s
                .split("::")
                .into_iter()
                .filter(|s| s.len() > 0)
                .map(|s| NamespaceChunk::from(s))
                .collect(),
        }
    }
}

impl NamespacePattern {
    pub fn matches(&self, path: &Vec<String>) -> bool {
        fn aux(pattern: &[NamespaceChunk], path: &[String]) -> bool {
            match (pattern, path) {
                ([], []) => true,
                ([NamespaceChunk::Exact(x), pattern @ ..], [y, path @ ..]) => {
                    x == y && aux(pattern, path)
                }
                ([NamespaceChunk::Glob(Glob::One), pattern @ ..], [_, path @ ..]) => {
                    aux(pattern, path)
                }
                ([NamespaceChunk::Glob(Glob::Many), pattern @ ..], []) => aux(pattern, path),
                ([NamespaceChunk::Glob(Glob::Many), pattern_tl @ ..], [_path_hd, path_tl @ ..]) => {
                    aux(pattern_tl, path) || aux(pattern, path_tl)
                }
                _ => false,
            }
        }
        aux(self.chunks.as_slice(), path.as_slice())
    }
}

#[derive(Debug, Clone)]
pub struct Options {
    pub inline_macro_calls: Vec<Namespace>,
}
