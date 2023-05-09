// rustc errors
extern crate rustc_errors;
use rustc_errors::DiagnosticId;

// rustc session
extern crate rustc_session;
use rustc_session::Session;

// rustc data_structures
extern crate rustc_data_structures;
use rustc_data_structures::sync::Lrc;

// rustc span
extern crate rustc_span;
use rustc_span::Span;

pub fn explicit_lifetime(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Explicit lifetimes are not supported",
        DiagnosticId::Lint {
            name: "Lifetime".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn mut_borrow_let(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Mutable borrows are not supported",
        DiagnosticId::Lint {
            name: "Mut borrow".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn extern_crate(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] External items need a model",
        DiagnosticId::Lint {
            name: "External".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_trait_objects(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Trait objects are not supported",
        DiagnosticId::Lint {
            name: "Trait objects".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_mut_self(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Mutable self is not supported",
        DiagnosticId::Lint {
            name: "Mutable self".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_mut(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Mutable arguments are not supported",
        DiagnosticId::Lint {
            name: "Mutability".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_assoc_items(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Associated items are not supported",
        DiagnosticId::Lint {
            name: "Assoc items".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn unsupported_item(session: &Lrc<Session>, span: Span, ident: String) {
    session.span_warn_with_code(
        span,
        format!("[Circus] {ident:?} is not supported"),
        DiagnosticId::Lint {
            name: "Unsupported item".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_fn_mut(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] FnMut is not supported",
        DiagnosticId::Lint {
            name: "Where".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_where_predicate(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Where predicates are not supported",
        DiagnosticId::Lint {
            name: "Where".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_async_await(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Async and await are not supported",
        DiagnosticId::Lint {
            name: "Async".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_unsafe(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Unsafe code is not supported",
        DiagnosticId::Lint {
            name: "Unsafe".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn unsupported_loop(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] loop and while are not supported",
        DiagnosticId::Lint {
            name: "Loops".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn no_union(session: &Lrc<Session>, span: Span) {
    session.span_warn_with_code(
        span,
        "[Circus] Unions are not supported",
        DiagnosticId::Lint {
            name: "Unsupported item".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}

pub fn derive_external_trait(session: &Lrc<Session>, span: Span, trait_name: String) {
    session.span_warn_with_code(
        span,
        format!("[Circus] Implementation of external trait {trait_name} will require a model"),
        DiagnosticId::Lint {
            name: "External trait".to_string(),
            has_future_breakage: false,
            is_force_warn: true,
        },
    );
}
