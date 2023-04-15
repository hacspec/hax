use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
pub struct Diagnostics<S> {
    kind: Kind,
    span: S,
    context: Option<String>,
}

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
#[repr(u16)]
pub enum Kind {
    UnsafeBlock = 0,
}

impl Kind {
    // https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
    pub fn discriminant(&self) -> u16 {
        unsafe { *(self as *const Self as *const u16) }
    }

    pub fn code(&self) -> String {
        // `C` stands for `circus`
        format!("CE{:0>4}", self.discriminant())
    }
}
