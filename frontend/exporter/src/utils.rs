macro_rules! format_with_context {
    ($format_str:expr $(,$arg:expr)* $(; {$($x:expr),*})?) => {
        format!(
            concat!(
                $format_str
                $(, "\n\nContext:\n", $(concat!(" - ", stringify!($x), ": "), "{:#?}", "\n",)*)?
            ),
            $($arg,)*
            $($($x,)*)?
        )
    };
    ($($tt:tt)*) => {format!($($tt)*)};
}

mod internal_helpers {
    macro_rules! _verb {
        (fatal, $o:expr, $message:expr) => {
            $o.struct_fatal($message)
        };
        (error, $o:expr, $message:expr) => {
            $o.struct_err($message)
        };
        (warn, $o:expr, $message:expr) => {
            $o.struct_warn($message)
        };
    }
    macro_rules! _span_verb_base {
        ($verb:ident, $s:ident, $span:expr, $message:expr) => {{
            let mut builder = $crate::utils::_verb!($verb, $s.base().tcx.sess, $message);
            if let Some(span) = $span {
                builder.set_span(span.clone());
            }
            builder.code(rustc_errors::DiagnosticId::Error(format!("HaxFront")));
            builder.note(
                "⚠️ This is a bug in Hax's frontend.
Please report this error with some context (e.g. the current crate)!",
            );
            builder.emit()
        }};
    }

    pub(crate) use _span_verb_base;
    pub(crate) use _verb;
}

macro_rules! report {
    ($verb:ident, $s:ident [$span:expr], $($tt:tt)*) => {
        $crate::utils::_span_verb_base!($verb, $s, Some($span), $crate::utils::format_with_context!($($tt)*))
    };
    ($verb:ident, $s:ident, $($tt:tt)*) => {
        $crate::utils::_span_verb_base!(
            $verb,
            $s,
            $s.base().opt_def_id.map(|did| $s.base().tcx.def_span(did)),
            $crate::utils::format_with_context!($($tt)*)
        )
    };
}

#[allow(unused_macros)]
macro_rules! error { ($($tt:tt)*) => {$crate::utils::report!(error, $($tt)*)} }
#[allow(unused_macros)]
macro_rules! warning { ($($tt:tt)*) => {$crate::utils::report!(warn, $($tt)*)} }
#[allow(unused_macros)]
macro_rules! fatal { ($($tt:tt)*) => {$crate::utils::report!(fatal, $($tt)*)} }

pub(crate) use format_with_context;
pub(crate) use internal_helpers::_span_verb_base;
pub(crate) use internal_helpers::_verb;
pub(crate) use report;

macro_rules! supposely_unreachable_message {
    ($label:literal) => {
        concat!(
            "Supposely unreachable place in the Rust AST. The label is ",
            stringify!($label),
            ".\nThis error report happend because some assumption about the Rust AST was broken."
        )
    };
}

macro_rules! supposely_unreachable {
    ($s:ident $([$span:expr])?, $label:literal $($tt:tt)*) => {
        {
            $crate::utils::error!($s$([$span])?, $crate::utils::supposely_unreachable_message!($label) $($tt)+)
        }
    };
}
macro_rules! supposely_unreachable_fatal {
    ($s:ident $([$span:expr])?, $label:literal $($tt:tt)*) => {
        $crate::utils::fatal!($s$([$span])?, $crate::utils::supposely_unreachable_message!($label) $($tt)+)
    };
}

pub(crate) use error;
pub(crate) use fatal;
pub(crate) use supposely_unreachable;
pub(crate) use supposely_unreachable_fatal;
pub(crate) use supposely_unreachable_message;
#[allow(unused_imports)]
pub(crate) use warning;
