module Barrett.Refinement_refinement
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_IsRefinement (v_Self: Type) = {
  f_InnerType:Type;
  f_refine_pre:f_InnerType -> bool;
  f_refine_post:f_InnerType -> v_Self -> bool;
  f_refine:x0: f_InnerType
    -> Prims.Pure v_Self (f_refine_pre x0) (fun result -> f_refine_post x0 result);
  f_value_pre:v_Self -> bool;
  f_value_post:v_Self -> f_InnerType -> bool;
  f_value:x0: v_Self
    -> Prims.Pure f_InnerType (f_value_pre x0) (fun result -> f_value_post x0 result)
}

type t_Refinement = | Refinement : u8 -> t_Refinement

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_IsRefinement t_Refinement =
  {
    f_InnerType = u8;
    f_refine_pre = (fun (x: u8) -> true);
    f_refine_post = (fun (x: u8) (out: t_Refinement) -> true);
    f_refine = (fun (x: u8) -> Refinement x <: t_Refinement);
    f_value_pre = (fun (self: t_Refinement) -> true);
    f_value_post = (fun (self: t_Refinement) (out: u8) -> true);
    f_value = fun (self: t_Refinement) -> self._0
  }
