module Core.Base.Seq
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Seq (v_T: Type0) = list v_T

type t_LIST (v_T: Type0) =
  | LIST_NIL : t_LIST v_T
  | LIST_CONS : v_T -> t_Seq v_T -> t_LIST v_T
