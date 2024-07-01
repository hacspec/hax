// rustc errors
extern crate rustc_errors;
use rustc_errors::DiagCtxtHandle;

// rustc data_structures
extern crate rustc_data_structures;

// rustc span
extern crate rustc_span;
use rustc_span::Span;

fn warn_span_lint(dcx: DiagCtxtHandle<'_>, span: Span, msg: impl AsRef<str>, lint_name: &str) {
    let mut err = dcx.struct_warn(msg.as_ref().to_string()).with_span(span);
    err.is_lint(lint_name.to_string(), /* has_future_breakage */ false);
    err.emit();
}

pub fn explicit_lifetime(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Explicit lifetimes are not supported",
        "Lifetime",
    );
}

pub fn mut_borrow_let(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Mutable borrows are not supported",
        "Mut borrow",
    );
}

pub fn extern_crate(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(dcx, span, "[Hax] External items need a model", "External");
}

pub fn no_trait_objects(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Trait objects are not supported",
        "Trait objects",
    );
}

pub fn no_mut_self(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Mutable self is not supported",
        "Mutable self",
    );
}

pub fn no_mut(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Mutable arguments are not supported",
        "Mutability",
    );
}

pub fn no_assoc_items(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Associated items are not supported",
        "Assoc items",
    );
}

pub fn unsupported_item(dcx: DiagCtxtHandle<'_>, span: Span, ident: String) {
    warn_span_lint(
        dcx,
        span,
        format!("[Hax] {ident:?} is not supported"),
        "Unsupported item",
    );
}

pub fn no_fn_mut(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(dcx, span, "[Hax] FnMut is not supported", "Where");
}

pub fn no_where_predicate(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Where predicates are not supported",
        "Where",
    );
}

pub fn no_async_await(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Async and await are not supported",
        "Async",
    );
}

pub fn no_unsafe(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(dcx, span, "[Hax] Unsafe code is not supported", "Unsafe");
}

pub fn unsupported_loop(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(dcx, span, "[Hax] loop and while are not supported", "Loops");
}

pub fn no_union(dcx: DiagCtxtHandle<'_>, span: Span) {
    warn_span_lint(
        dcx,
        span,
        "[Hax] Unions are not supported",
        "Unsupported item",
    );
}

pub fn derive_external_trait(dcx: DiagCtxtHandle<'_>, span: Span, trait_name: String) {
    warn_span_lint(
        dcx,
        span,
        format!("[Hax] Implementation of external trait {trait_name} will require a model"),
        "External trait",
    );
}
