module Core.Option
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Option (v_T: Type0) =
  | Option_None : t_Option v_T
  | Option_Some : v_T -> t_Option v_T
