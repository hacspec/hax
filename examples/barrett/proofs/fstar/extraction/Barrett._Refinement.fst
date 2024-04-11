module Barrett._Refinement
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Refinement = | Refinement : u8 -> t_Refinement

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Barrett.t_IsRefinement t_Refinement =
  {
    f_InnerType = u8;
    f_refine_pre = (fun (x: u8) -> true);
    f_refine_post = (fun (x: u8) (out: t_Refinement) -> true);
    f_refine = (fun (x: u8) -> Refinement x <: t_Refinement);
    f_value_pre = (fun (self: t_Refinement) -> true);
    f_value_post = (fun (self: t_Refinement) (out: u8) -> true);
    f_value = fun (self: t_Refinement) -> self._0
  }
