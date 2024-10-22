use crate::prelude::*;
use crate::sinto_todo;

/// Reflects [`rustc_span::Loc`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
}

/// Reflects [`rustc_span::hygiene::DesugaringKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::DesugaringKind, state: S as _s)]
pub enum DesugaringKind {
    CondTemporary,
    QuestionMark,
    TryBlock,
    YeetExpr,
    OpaqueTy,
    Async,
    Await,
    ForLoop,
    WhileLoop,
    BoundModifier,
}

/// Reflects [`rustc_span::hygiene::AstPass`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::AstPass, state: S as _s)]
pub enum AstPass {
    StdImports,
    TestHarness,
    ProcMacroHarness,
}

/// Reflects [`rustc_span::hygiene::MacroKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::MacroKind, state: S as _s)]
pub enum MacroKind {
    Bang,
    Attr,
    Derive,
}

/// Reflects [`rustc_span::hygiene::ExpnKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_span::hygiene::ExpnKind, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ExpnKind {
    Root,
    Macro(MacroKind, Symbol),
    AstPass(AstPass),
    Desugaring(DesugaringKind),
}

/// Reflects [`rustc_span::edition::Edition`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_span::edition::Edition, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Edition {
    Edition2015,
    Edition2018,
    Edition2021,
    Edition2024,
}

/// Reflects [`rustc_span::hygiene::ExpnData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_span::hygiene::ExpnData, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ExpnData {
    pub kind: ExpnKind,
    // pub parent: Box<ExpnData>,
    pub call_site: Span,
    pub def_site: Span,
    #[map(x.as_ref().map(|x| x.clone().iter().map(|x|x.sinto(state)).collect()))]
    pub allow_internal_unstable: Option<Vec<Symbol>>,
    pub edition: Edition,
    pub macro_def_id: Option<DefId>,
    pub parent_module: Option<DefId>,
    pub local_inner_macros: bool,
}

/// Reflects [`rustc_span::Span`]
#[derive(::serde::Serialize, ::serde::Deserialize, Clone, Debug, JsonSchema, Eq, Ord)]
pub struct Span {
    pub lo: Loc,
    pub hi: Loc,
    pub filename: FileName,
    /// Original rustc span; can be useful for reporting rustc
    /// diagnostics (this is used in Charon)
    #[cfg(feature = "rustc")]
    #[serde(skip)]
    pub rust_span_data: Option<rustc_span::SpanData>,
    #[cfg(not(feature = "rustc"))]
    #[serde(skip)]
    pub rust_span_data: Option<()>,
    // expn_backtrace: Vec<ExpnData>,
}

/// We need to define manual `impl`s of `Span`: we want to skip the
/// field `rust_span_data`. The derive macros from `bincode` don't
/// allow that, see https://github.com/bincode-org/bincode/issues/452.
const _: () = {
    impl bincode::Encode for Span {
        fn encode<E: bincode::enc::Encoder>(
            &self,
            encoder: &mut E,
        ) -> core::result::Result<(), bincode::error::EncodeError> {
            bincode::Encode::encode(&self.lo, encoder)?;
            bincode::Encode::encode(&self.hi, encoder)?;
            bincode::Encode::encode(&self.filename, encoder)?;
            Ok(())
        }
    }

    impl bincode::Decode for Span {
        fn decode<D: bincode::de::Decoder>(
            decoder: &mut D,
        ) -> core::result::Result<Self, bincode::error::DecodeError> {
            Ok(Self {
                lo: bincode::Decode::decode(decoder)?,
                hi: bincode::Decode::decode(decoder)?,
                filename: bincode::Decode::decode(decoder)?,
                rust_span_data: None,
            })
        }
    }

    impl<'de> bincode::BorrowDecode<'de> for Span {
        fn borrow_decode<D: bincode::de::BorrowDecoder<'de>>(
            decoder: &mut D,
        ) -> core::result::Result<Self, bincode::error::DecodeError> {
            Ok(Self {
                lo: bincode::BorrowDecode::borrow_decode(decoder)?,
                hi: bincode::BorrowDecode::borrow_decode(decoder)?,
                filename: bincode::BorrowDecode::borrow_decode(decoder)?,
                rust_span_data: None,
            })
        }
    }
};

const _: () = {
    // `rust_span_data` is a metadata that should *not* be taken into
    // account while hashing or comparing

    impl std::hash::Hash for Span {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.lo.hash(state);
            self.hi.hash(state);
            self.filename.hash(state);
        }
    }
    impl PartialEq for Span {
        fn eq(&self, other: &Self) -> bool {
            self.lo == other.lo && self.hi == other.hi && self.filename == other.filename
        }
    }

    impl PartialOrd for Span {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(
                self.lo.partial_cmp(&other.lo)?.then(
                    self.hi
                        .partial_cmp(&other.hi)?
                        .then(self.filename.partial_cmp(&other.filename)?),
                ),
            )
        }
    }
};

#[cfg(feature = "rustc")]
impl From<rustc_span::Loc> for Loc {
    fn from(val: rustc_span::Loc) -> Self {
        Loc {
            line: val.line,
            col: val.col_display,
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx>> SInto<S, Span> for rustc_span::Span {
    fn sinto(&self, s: &S) -> Span {
        if let Some(span) = s.with_global_cache(|cache| cache.spans.get(self).cloned()) {
            return span;
        }
        let span = translate_span(*self, s.base().tcx.sess);
        s.with_global_cache(|cache| cache.spans.insert(*self, span.clone()));
        span
    }
}

/// Reflects [`rustc_span::source_map::Spanned`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}
#[cfg(feature = "rustc")]
impl<'s, S: UnderOwnerState<'s>, T: SInto<S, U>, U> SInto<S, Spanned<U>>
    for rustc_span::source_map::Spanned<T>
{
    fn sinto<'a>(&self, s: &S) -> Spanned<U> {
        Spanned {
            node: self.node.sinto(s),
            span: self.span.sinto(s),
        }
    }
}

impl<'tcx, S> SInto<S, PathBuf> for PathBuf {
    fn sinto(&self, _: &S) -> PathBuf {
        self.clone()
    }
}

/// Reflects [`rustc_span::RealFileName`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[args(<S>, from: rustc_span::RealFileName, state: S as _s)]
pub enum RealFileName {
    LocalPath(PathBuf),
    Remapped {
        local_path: Option<PathBuf>,
        virtual_name: PathBuf,
    },
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, u64> for rustc_data_structures::stable_hasher::Hash64 {
    fn sinto(&self, _: &S) -> u64 {
        self.as_u64()
    }
}

/// Reflects [`rustc_span::FileName`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_span::FileName, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FileName {
    Real(RealFileName),
    QuoteExpansion(u64),
    Anon(u64),
    MacroExpansion(u64),
    ProcMacroSourceCode(u64),
    CliCrateAttr(u64),
    Custom(String),
    // #[map(FileName::DocTest(x.0.to_str().unwrap().into()))]
    #[custom_arm(FROM_TYPE::DocTest(x, _) => TO_TYPE::DocTest(x.to_str().unwrap().into()),)]
    DocTest(String),
    InlineAsm(u64),
}

impl FileName {
    pub fn to_string(&self) -> String {
        match self {
            Self::Real(RealFileName::LocalPath(path))
            | Self::Real(RealFileName::Remapped {
                local_path: Some(path),
                ..
            })
            | Self::Real(RealFileName::Remapped {
                virtual_name: path, ..
            }) => format!("{}", path.display()),
            _ => format!("{:?}", self),
        }
    }
    pub fn to_path(&self) -> Option<&std::path::Path> {
        match self {
            Self::Real(RealFileName::LocalPath(path))
            | Self::Real(RealFileName::Remapped {
                local_path: Some(path),
                ..
            })
            | Self::Real(RealFileName::Remapped {
                virtual_name: path, ..
            }) => Some(path),
            _ => None,
        }
    }
}

sinto_todo!(rustc_span, ErrorGuaranteed);
