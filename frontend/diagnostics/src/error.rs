// rustc errors
extern crate rustc_errors;
use rustc_errors::{DiagCtxt, DiagnosticId};

// rustc data_structures
extern crate rustc_data_structures;

// rustc span
extern crate rustc_span;
use rustc_span::Span;

pub fn explicit_lifetime(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Explicit lifetimes are not supported",
        DiagnosticId::Lint {
            name: "Lifetime".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn mut_borrow_let(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Mutable borrows are not supported",
        DiagnosticId::Lint {
            name: "Mut borrow".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn extern_crate(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] External items need a model",
        DiagnosticId::Lint {
            name: "External".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_trait_objects(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Trait objects are not supported",
        DiagnosticId::Lint {
            name: "Trait objects".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_mut_self(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Mutable self is not supported",
        DiagnosticId::Lint {
            name: "Mutable self".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_mut(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Mutable arguments are not supported",
        DiagnosticId::Lint {
            name: "Mutability".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_assoc_items(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Associated items are not supported",
        DiagnosticId::Lint {
            name: "Assoc items".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn unsupported_item(dcx: &DiagCtxt, span: Span, ident: String) {
    dcx.span_warn_with_code(
        span,
        format!("[Hax] {ident:?} is not supported"),
        DiagnosticId::Lint {
            name: "Unsupported item".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_fn_mut(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] FnMut is not supported",
        DiagnosticId::Lint {
            name: "Where".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_where_predicate(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Where predicates are not supported",
        DiagnosticId::Lint {
            name: "Where".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_async_await(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Async and await are not supported",
        DiagnosticId::Lint {
            name: "Async".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_unsafe(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Unsafe code is not supported",
        DiagnosticId::Lint {
            name: "Unsafe".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn unsupported_loop(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] loop and while are not supported",
        DiagnosticId::Lint {
            name: "Loops".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_union(dcx: &DiagCtxt, span: Span) {
    dcx.span_warn_with_code(
        span,
        "[Hax] Unions are not supported",
        DiagnosticId::Lint {
            name: "Unsupported item".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn derive_external_trait(dcx: &DiagCtxt, span: Span, trait_name: String) {
    dcx.span_warn_with_code(
        span,
        format!("[Hax] Implementation of external trait {trait_name} will require a model"),
        DiagnosticId::Lint {
            name: "External trait".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}
