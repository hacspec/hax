module Core.Base.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_HaxInt = Prims.nat

type t_Positive = Prims.pos

type t_POS =
  | POS_ZERO : t_POS
  | POS_POS : t_Positive -> t_POS

type t_POSITIVE =
  | POSITIVE_XH : t_POSITIVE
  | POSITIVE_XO : t_Positive -> t_POSITIVE
  | POSITIVE_XI : t_Positive -> t_POSITIVE

type t_Unary = nat

type t_UNARY =
  | UNARY_ZERO : t_UNARY
  | UNARY_SUCC : t_Unary -> t_UNARY
