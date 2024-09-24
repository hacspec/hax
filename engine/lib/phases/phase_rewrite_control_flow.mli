(** This phase finds control flow expression (`if` or `match`) with a `return` expression
    in one of the branches. We replace them by replicating what comes after in all the branches. 
    This allows the `return` to be eliminated by `drop_needless_returns`.
    This phase should come after phase_local_mutation. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
