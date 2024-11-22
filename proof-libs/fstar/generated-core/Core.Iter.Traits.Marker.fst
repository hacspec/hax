module Core.Iter.Traits.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_TrustedFused (v_Self: Type0) = { __marker_trait_t_TrustedFused:Prims.unit }

class t_TrustedStep (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13722385431118852294:Core.Iter.Range.t_Step v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self
}

class t_FusedIterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15444444506782437531:Core.Iter.Traits.Iterator.t_Iterator
  v_Self
}

class t_TrustedLen (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15444444506782437531:Core.Iter.Traits.Iterator.t_Iterator
  v_Self
}
