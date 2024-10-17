use hax_adt_into::derive_group;
use schemars::JsonSchema;

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema)]
pub enum Glob {
    One,  // *
    Many, // **
}

impl ToString for Glob {
    fn to_string(&self) -> String {
        match self {
            Self::One => "*",
            Self::Many => "**",
        }
        .to_string()
    }
}

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema)]
pub enum NamespaceChunk {
    Glob(Glob),
    Exact(String),
}

impl ToString for NamespaceChunk {
    fn to_string(&self) -> String {
        match self {
            Self::Glob(glob) => glob.to_string(),
            Self::Exact(string) => string.to_string(),
        }
    }
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

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema)]
pub struct Namespace {
    pub chunks: Vec<NamespaceChunk>,
}

impl ToString for Namespace {
    fn to_string(&self) -> String {
        self.chunks
            .iter()
            .map(NamespaceChunk::to_string)
            .collect::<Vec<_>>()
            .join("::")
            .to_string()
    }
}

impl std::convert::From<String> for Namespace {
    fn from(s: String) -> Self {
        Namespace {
            chunks: s
                .split("::")
                .filter(|s| !s.is_empty())
                .map(NamespaceChunk::from)
                .collect(),
        }
    }
}

impl Namespace {
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
