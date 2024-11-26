module Core.Base.Spec.Z
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Z =
  | Z_NEG : Core.Base.Spec.Binary.Positive.t_Positive -> t_Z
  | Z_ZERO : t_Z
  | Z_POS : Core.Base.Spec.Binary.Positive.t_Positive -> t_Z

let v_Z_ONE: t_Z = Z_POS Core.Base.Spec.Binary.Positive.xH <: t_Z

let v_Z_TWO: t_Z =
  Z_POS
  (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Haxint.v_HaxInt_TWO
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  t_Z
