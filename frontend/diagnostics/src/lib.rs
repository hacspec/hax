#![feature(rustc_private)]

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub mod error;

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
pub struct Diagnostics<S> {
    pub kind: Kind,
    pub span: S,
    pub context: String,
}

impl<S> std::fmt::Display for Diagnostics<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}: {:?}", self.context, self.kind)
    }
}

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
#[repr(u16)]
pub enum Kind {
    /// Unsafe code is not supported
    UnsafeBlock = 0,

    /// A feature is not currently implemented, but
    Unimplemented {
        /// Issue on the GitHub repository
        issue_id: Option<u32>,
        details: Option<String>,
    } = 1,

    /// Unknown error
    // This is useful when doing sanity checks (i.e. one can yield
    // this error kind for cases that should never happen)
    Unknown { details: Option<String> } = 2,

    /// Unallowed mutable reference
    UnallowedMutRef = 3,
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
