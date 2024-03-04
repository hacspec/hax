(** This phase adds specification to traits. For each method `f` in a
trait, we add a `f_pre` and a `f_post`. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
