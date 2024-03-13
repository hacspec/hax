(** This phase transforms `return e` expressions into `e` when `return
e` is on an exit position. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
