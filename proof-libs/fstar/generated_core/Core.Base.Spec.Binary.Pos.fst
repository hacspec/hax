module Core.Base.Spec.Binary.Pos
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_POS =
  | POS_ZERO : t_POS
  | POS_POS : Core.Base.Spec.Binary.Positive.t_Positive -> t_POS

let match_pos (s: Core.Base.Spec.Haxint.t_HaxInt) : t_POS =
  if
    Core.Base.Spec.Haxint.is_zero (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          s
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  then POS_ZERO <: t_POS
  else POS_POS (Core.Base.Spec.Binary.Positive.positive_from_int s) <: t_POS
