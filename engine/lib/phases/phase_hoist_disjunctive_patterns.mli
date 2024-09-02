(** This phase eliminates nested disjunctive patterns (leaving 
    only shallow disjunctions). It moves the disjunctions up 
    to the top-level pattern. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
