//! This module re-exports macros from `hax-lib-macros` since a
//! proc-macro crate cannot export anything but procedural macros.

pub use hax_lib_macros::{
    attributes, ensures, exclude, impl_fn_decoration, include, interface, lemma, loop_invariant, opaque_type,
    refinement_type, requires, trait_fn_decoration,
};

pub use hax_lib_macros::{
    process_init, process_read, process_write, protocol_messages, pv_constructor, pv_handwritten,
};

macro_rules! export_quoting_proc_macros {
    ($backend:ident($expr_name:ident, $expr_unsafe_name:ident, $before_name:ident, $after_name:ident, $replace_name:ident, $cfg_name:ident $(, {$($extra:tt)+})?)) => {
        pub use hax_lib_macros::$expr_name as $backend;
        #[doc(hidden)]
        pub use hax_lib_macros::$expr_unsafe_name;

        #[doc=concat!("Procedural macros for ", stringify!($backend))]
        pub mod $backend {
            pub use hax_lib_macros::$after_name as after;
            pub use hax_lib_macros::$before_name as before;
            pub use hax_lib_macros::$replace_name as replace;
            $($($extra)*)?
        }
    };

    ($backend:ident $payload:tt $($others:tt)+) => {
        export_quoting_proc_macros!($backend$payload);
        export_quoting_proc_macros!($($others)+);
    }
}

export_quoting_proc_macros!(
    fstar(fstar_expr, fstar_unsafe_expr, fstar_before, fstar_after, fstar_replace, hax_backend_fstar, {
        pub use hax_lib_macros::fstar_options as options;
        pub use hax_lib_macros::fstar_verification_status as verification_status;
    })

    coq(coq_expr, coq_unsafe_expr, coq_before, coq_after, coq_replace, hax_backend_coq)

    proverif(proverif_expr, proverif_unsafe_expr, proverif_before, proverif_after, proverif_replace, hax_backend_proverif));
