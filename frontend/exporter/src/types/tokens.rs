//! Copies of types related to tokens and syntax representation of rust, as well as macros.
use crate::prelude::*;

/// Reflects [`rustc_ast::token::Delimiter`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::Delimiter, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
    Invisible,
}

/// Reflects [`rustc_ast::tokenstream::TokenTree`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::tokenstream::TokenTree, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenTree {
    Token(Token, Spacing),
    Delimited(DelimSpan, DelimSpacing, Delimiter, TokenStream),
}

sinto_todo!(rustc_ast::tokenstream, DelimSpan);
sinto_todo!(rustc_ast::tokenstream, DelimSpacing);

/// Reflects [`rustc_ast::tokenstream::Spacing`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::tokenstream::Spacing, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Spacing {
    Alone,
    Joint,
    JointHidden,
}

/// Reflects [`rustc_ast::token::BinOpToken`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::BinOpToken, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOpToken {
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    And,
    Or,
    Shl,
    Shr,
}

/// Reflects [`rustc_ast::token::TokenKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::token::TokenKind, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenKind {
    Eq,
    Lt,
    Le,
    EqEq,
    Ne,
    Ge,
    Gt,
    AndAnd,
    OrOr,
    Not,
    Tilde,
    BinOp(BinOpToken),
    BinOpEq(BinOpToken),
    At,
    Dot,
    DotDot,
    DotDotDot,
    DotDotEq,
    Comma,
    Semi,
    Colon,
    RArrow,
    LArrow,
    FatArrow,
    Pound,
    Dollar,
    Question,
    SingleQuote,
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
    // Literal(l: Lit),
    Ident(Symbol, bool),
    Lifetime(Symbol),
    // Interpolated(n: Nonterminal),
    // DocComment(k: CommentKind, ats: AttrStyle, s: Symbol),
    Eof,
    #[todo]
    Todo(String),
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, bool> for rustc_ast::token::IdentIsRaw {
    fn sinto(&self, _s: &S) -> bool {
        match self {
            Self::Yes => true,
            Self::No => false,
        }
    }
}

/// Reflects [`rustc_ast::token::Token`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::token::Token, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// Reflects [`rustc_ast::ast::DelimArgs`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::DelimArgs, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DelimArgs {
    pub dspan: DelimSpan,
    pub delim: Delimiter,
    pub tokens: TokenStream,
}

/// Reflects [`rustc_ast::ast::MacCall`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::ast::MacCall, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MacCall {
    #[map(x.segments.iter().map(|rustc_ast::ast::PathSegment{ident, ..}| ident.as_str().into()).collect())]
    pub path: Path,
    pub args: DelimArgs,
}

/// Reflects [`rustc_ast::tokenstream::TokenStream`] as a plain
/// string. If you need to reshape that into Rust tokens or construct,
/// please use, e.g., `syn`.
pub type TokenStream = String;

#[cfg(feature = "rustc")]
impl<'t, S> SInto<S, TokenStream> for rustc_ast::tokenstream::TokenStream {
    fn sinto(&self, _: &S) -> String {
        rustc_ast_pretty::pprust::tts_to_string(self)
    }
}
