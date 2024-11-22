module Core.Iter.Traits.Iterator
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Iterator (v_Self: Type0) = {
  f_Item:Type0;
  f_next_pre:v_Self -> Type0;
  f_next_post:v_Self -> (v_Self & Core.Option.t_Option f_Item) -> Type0;
  f_next:x0: v_Self
    -> Prims.Pure (v_Self & Core.Option.t_Option f_Item)
        (f_next_pre x0)
        (fun result -> f_next_post x0 result);
  f_size_hint_pre:v_Self -> Type0;
  f_size_hint_post:v_Self -> (usize & Core.Option.t_Option usize) -> Type0;
  f_size_hint:x0: v_Self
    -> Prims.Pure (usize & Core.Option.t_Option usize)
        (f_size_hint_pre x0)
        (fun result -> f_size_hint_post x0 result);
  f_fold_pre:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i4: Core.Ops.Function.t_FnMut v_F (v_B & f_Item) |} ->
      v_Self ->
      v_B ->
      v_F
    -> Type0;
  f_fold_post:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i4: Core.Ops.Function.t_FnMut v_F (v_B & f_Item) |} ->
      v_Self ->
      v_B ->
      v_F ->
      v_B
    -> Type0;
  f_fold:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i4: Core.Ops.Function.t_FnMut v_F (v_B & f_Item) |} ->
      x0: v_Self ->
      x1: v_B ->
      x2: v_F
    -> Prims.Pure v_B
        (f_fold_pre #v_B #v_F #i4 x0 x1 x2)
        (fun result -> f_fold_post #v_B #v_F #i4 x0 x1 x2 result)
}
