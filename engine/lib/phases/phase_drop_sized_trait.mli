(** This phase remove any occurence to the `core::marker::sized`
trait. This trait appears a lot, but is generally not very useful in
our backends. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
