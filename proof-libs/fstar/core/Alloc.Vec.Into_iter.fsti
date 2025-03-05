module Alloc.Vec.Into_iter

val t_IntoIter (t: Type0) (_: unit): Type0

[@@ FStar.Tactics.Typeclasses.tcinstance]
val into_iter_into_iterator (t: Type0): 
  Core.Iter.Traits.Collect.t_IntoIterator (t_IntoIter t Alloc.Alloc.t_Global)
