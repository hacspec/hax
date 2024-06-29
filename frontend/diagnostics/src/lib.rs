#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_error_messages;
extern crate rustc_errors;
extern crate rustc_session;
extern crate rustc_span;

use colored::Colorize;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub mod report;

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
pub struct Diagnostics {
    pub kind: Kind,
    pub span: Vec<hax_frontend_exporter::Span>,
    pub context: String,
}

impl std::fmt::Display for Diagnostics {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({}) ", self.context)?;
        match &self.kind {
            Kind::Unimplemented { issue_id, details } => write!(
                f,
                "something is not implemented yet.{}{}",
                match issue_id {
                    Some(id) => format!("This is discussed in issue https://github.com/hacspec/hax/issues/{id}.\nPlease upvote or comment this issue if you see this error message."),
                    _ => "".to_string(),
                },
                match details {
                    Some(details) => format!("\n{}", details),
                    _ => "".to_string(),
                }
            ),
            Kind::UnsupportedMacro { id } => write!(
                f,
                "The unexpanded macro {} it is not supported by this backend. Please verify the option you passed the {} (or {}) option.",
                id.bold(),
                "--inline-macro-call".bold(), "-i".bold()
            ),
            Kind::UnsafeBlock => write!(f, "Unsafe blocks are not allowed."),
            Kind::AssertionFailure {details} => write!(
                f,
                "Fatal error: something we considered as impossible occurred! {}\nDetails: {}",
                "Please report this by submitting an issue on GitHub!".bold(),
                details
            ),
            Kind::UnallowedMutRef => write!(
                f,
                "The mutation of this {} is not allowed here.",
                "&mut".bold()
            ),
            Kind::ExpectedMutRef => write!(
                f,
                "At this position, Hax was expecting an expression of the shape `&mut _`. Hax forbids `f(x)` (where `f` expects a mutable reference as input) when `x` is not a {}{} or when it is a dereference expression.

{}
",
                "place expression".bold(),
                "[1]".bright_black(),
                "[1]: https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions"
            ),
            Kind::ClosureMutatesParentBindings {bindings} => write!(
                f,
                "The bindings {:?} cannot be mutated here: they don't belong to the closure scope, and this is not allowed.",
                bindings
            ),
            Kind::ArbitraryLHS => write!(f, "Assignation of an arbitrary left-hand side is not supported. `lhs = e` is fine only when `lhs` is a combination of local identifiers, field accessors and index accessors."),

            Kind::AttributeRejected {reason} => write!(f, "Here, this attribute cannot be used: {reason}."),
            _ => write!(f, "{:?}", self.kind),
        }
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
    AssertionFailure {
        details: String,
    } = 2,

    /// Unallowed mutable reference
    UnallowedMutRef = 3,

    /// Unsupported macro invokation
    UnsupportedMacro {
        id: String,
    } = 4,

    /// Error parsing a macro invocation to a macro treated specifcially by a backend
    ErrorParsingMacroInvocation {
        macro_id: String,
        details: String,
    } = 5,

    /// Mutation of bindings living outside a closure scope are not supported
    ClosureMutatesParentBindings {
        bindings: Vec<String>,
    } = 6,

    /// Assignation of an arbitrary left-hand side is not supported. `lhs = e` is fine only when `lhs` is a combination of local identifiers, field accessors and index accessors.
    ArbitraryLHS = 7,

    /// A phase explicitely rejected this chunk of code
    ExplicitRejection {
        reason: String,
    } = 8,

    /// A backend doesn't support a tuple size
    UnsupportedTupleSize {
        tuple_size: u32,
        reason: String,
    } = 9,

    ExpectedMutRef = 10,

    /// An hax attribute (from `hax-lib-macros`) was rejected
    AttributeRejected {
        reason: String,
    },
}

impl Kind {
    // https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
    pub fn discriminant(&self) -> u16 {
        unsafe { *(self as *const Self as *const u16) }
    }

    pub fn code(&self) -> String {
        format!("HAX{:0>4}", self.discriminant())
    }
}
