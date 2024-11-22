module Core.Iter.Traits.Collect
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_IntoIterator (v_Self: Type0) = {
  f_Item:Type0;
  f_IntoIter:Type0;
  f_IntoIter_11554253487815790481:Core.Iter.Traits.Iterator.t_Iterator f_IntoIter;
  f_into_iter_pre:v_Self -> Type0;
  f_into_iter_post:v_Self -> f_IntoIter -> Type0;
  f_into_iter:x0: v_Self
    -> Prims.Pure f_IntoIter (f_into_iter_pre x0) (fun result -> f_into_iter_post x0 result)
}

class t_FromIterator (v_Self: Type0) (v_A: Type0) = {
  f_from_iter_pre:#v_T: Type0 -> {| i1: t_IntoIterator v_T |} -> v_T -> Type0;
  f_from_iter_post:#v_T: Type0 -> {| i1: t_IntoIterator v_T |} -> v_T -> v_Self -> Type0;
  f_from_iter:#v_T: Type0 -> {| i1: t_IntoIterator v_T |} -> x0: v_T
    -> Prims.Pure v_Self
        (f_from_iter_pre #v_T #i1 x0)
        (fun result -> f_from_iter_post #v_T #i1 x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Iter.Traits.Iterator.t_Iterator v_I)
    : t_IntoIterator v_I =
  {
    f_Item = i1.f_Item;
    f_IntoIter = v_I;
    f_IntoIter_11554253487815790481 = FStar.Tactics.Typeclasses.solve;
    f_into_iter_pre = (fun (self: v_I) -> true);
    f_into_iter_post = (fun (self: v_I) (out: v_I) -> true);
    f_into_iter = fun (self: v_I) -> self
  }
