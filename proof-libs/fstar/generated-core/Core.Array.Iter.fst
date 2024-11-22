module Core.Array.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_IntoIter (v_T: Type0) (v_N: usize) = {
  f_data:Core.Primitive.t_Array v_T v_N;
  f_alive:Core.Ops.Index_range.t_IndexRange
}
