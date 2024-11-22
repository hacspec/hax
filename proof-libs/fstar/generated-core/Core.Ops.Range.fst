module Core.Ops.Range
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Range (v_Idx: Type0) = {
  f_start:v_Idx;
  f_end:v_Idx
}
