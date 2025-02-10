module Alloc.Vec.Drain

val t_Drain: Type0 -> unit -> Type0

[@FStar.Tactics.Typeclasses.tcinstance]
val iterator_drain t a: Core.Iter.Traits.Iterator.iterator (t_Drain t a)
