use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
pub struct Diagnostics<S> {
    pub kind: Kind,
    pub span: S,
    pub context: Option<String>,
}

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
#[repr(u16)]
pub enum Kind {
    UnsafeBlock = 0,
    Unimplemented { details: Option<String> } = 1,
    Unknown { details: Option<String> } = 2,
    // ThirErrLiteral = 3,
    // | LetElse
    // | LetWithoutInit
    // BadSpanUnion = 4,
    // | ShallowMutUnsupported
    // | GotTypeInLitPat
    // | IllTypedIntLiteral
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
