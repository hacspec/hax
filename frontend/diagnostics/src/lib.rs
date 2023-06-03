#![feature(rustc_private)]

extern crate rustc_errors;
extern crate rustc_session;
extern crate rustc_span;

use colored::Colorize;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub trait SessionExtTrait {
    fn span_hax_err(&self, diag: Diagnostics<rustc_span::Span>);
}
impl SessionExtTrait for rustc_session::Session {
    fn span_hax_err(&self, diag: Diagnostics<rustc_span::Span>) {
        self.span_err_with_code(
            diag.span,
            format!("{}", diag),
            rustc_errors::DiagnosticId::Error(diag.kind.code().into()),
        );
    }
}

pub mod error;

#[derive(Debug, Clone, JsonSchema, Serialize, Deserialize)]
pub struct Diagnostics<S> {
    pub kind: Kind,
    pub span: S,
    pub context: String,
}

impl<S> Diagnostics<S> {
    pub fn set_span<T>(&self, span: T) -> Diagnostics<T> {
        Diagnostics {
            kind: self.kind.clone(),
            context: self.context.clone(),
            span,
        }
    }
}

impl<S> std::fmt::Display for Diagnostics<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.kind {
            Kind::Unimplemented { issue_id, details } => write!(
                f,
                "{}: something is not implemented yet.{}{}",
                self.context,
                match issue_id {
                    Some(id) => format!("This is discussed in issue https://github.com/hacspec/hacspec-v2/issues/{id}.\nPlease upvote or comment this issue if you see this error message."),
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
            Kind::ClosureMutatesParentBindings {bindings} => write!(
                f,
                "The bindings {:?} cannot be mutated here: they don't belong to the closure scope, and this is not allowed.",
                bindings
            ),
            Kind::ArbitraryLHS => write!(f, "Assignation of an arbitrary left-hand side is not supported. [lhs = e] is fine only when [lhs] is a combination of local identifiers, field accessors and index accessors."),
            _ => write!(f, "{}: {:?}", self.context, self.kind),
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
    AssertionFailure { details: String } = 2,

    /// Unallowed mutable reference
    UnallowedMutRef = 3,

    /// Unsupported macro invokation
    UnsupportedMacro { id: String } = 4,

    /// Error parsing a macro invocation to a macro treated specifcially by a backend
    ErrorParsingMacroInvocation { macro_id: String, details: String } = 5,

    /// Mutation of bindings living outside a closure scope are not supported
    ClosureMutatesParentBindings { bindings: Vec<String> } = 6,

    /// Assignation of an arbitrary left-hand side is not supported. [lhs = e] is fine only when [lhs] is a combination of local identifiers, field accessors and index accessors.
    ArbitraryLHS = 7,

    /// A phase explicitely rejected this chunk of code
    ExplicitRejection { reason: String } = 8,

    /// A backend doesn't support a tuple size
    UnsupportedTupleSize { tuple_size: u32, reason: String } = 9,
}

impl Kind {
    // https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
    pub fn discriminant(&self) -> u16 {
        unsafe { *(self as *const Self as *const u16) }
    }

    pub fn code(&self) -> String {
        // `C` stands for `hax`
        format!("CE{:0>4}", self.discriminant())
    }
}
