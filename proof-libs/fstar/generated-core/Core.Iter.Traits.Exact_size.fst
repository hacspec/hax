module Core.Iter.Traits.Exact_size
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_ExactSizeIterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15444444506782437531:Core.Iter.Traits.Iterator.t_Iterator
  v_Self;
  f_len_pre:v_Self -> Type0;
  f_len_post:v_Self -> usize -> Type0;
  f_len:x0: v_Self -> Prims.Pure usize (f_len_pre x0) (fun result -> f_len_post x0 result);
  f_is_empty_pre:v_Self -> Type0;
  f_is_empty_post:v_Self -> bool -> Type0;
  f_is_empty:x0: v_Self
    -> Prims.Pure bool (f_is_empty_pre x0) (fun result -> f_is_empty_post x0 result)
}
