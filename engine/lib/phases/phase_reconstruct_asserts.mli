(** This phase recognizes desugared `assert!(...)` to rewrite 
    into `hax_lib::assert(..)`. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
