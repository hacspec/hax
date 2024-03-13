(** This phase rewrites `let pat = match ... { ... => ..., ... => return ... }; e`
    into `match ... { ... => let pat = ...; e}`. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
