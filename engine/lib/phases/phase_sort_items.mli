(** This phase sorts items so that each item comes after the items it depends on.
    This is done by sorting namespaces with the same property, and then sorting 
    items within each namespace, trying as much as possible to respect the 
    original order. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
