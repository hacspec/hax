module Core.Iter.Traits.Collect

open Rust_primitives

class t_IntoIterator self = {
  f_IntoIter: Type0;
  // f_Item: Type0;
  f_into_iter: self -> f_IntoIter;
}

unfold instance impl t {| Core.Iter.Traits.Iterator.iterator t |}: t_IntoIterator t = {
  f_IntoIter = t;
  f_into_iter = id;
}

class t_Extend
  (v_Self: Type0) (v_A: Type0)
  = {
  f_extend_pre:
      #v_T: Type0 ->
      {| i1:
          Core.Iter.Traits.Collect.t_IntoIterator
          v_T |} ->
      v_Self ->
      v_T
    -> Type0;
  f_extend_post:
      #v_T: Type0 ->
      {| i1:
          Core.Iter.Traits.Collect.t_IntoIterator
          v_T |} ->
      v_Self ->
      v_T ->
      v_Self
    -> Type0;
  f_extend:
      #v_T: Type0 ->
      {| i1:
          Core.Iter.Traits.Collect.t_IntoIterator
          v_T |} ->
      x0: v_Self ->
      x1: v_T
    -> Prims.Pure v_Self
        (f_extend_pre #v_T #i1 x0 x1)
        (fun result ->
            f_extend_post #v_T
              #i1
              x0
              x1
              result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val iter_extend v_Self {| i1: Core.Iter.Traits.Iterator.iterator v_Self |}:
  t_Extend v_Self (i1.f_Item)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val extend_slice (t: eqtype): t_Extend (t_Slice t) t
