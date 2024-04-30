(** This phase specializes certain specific method applications
(according to their name and the type it is being used on) into plain
functions.

This is useful espcially for math integers: the methods of the traits
`Add`, `Sub`, `Mul` etc. are mapped to "primitive" functions in
backends (e.g. Prims.whatever in FStar). *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
