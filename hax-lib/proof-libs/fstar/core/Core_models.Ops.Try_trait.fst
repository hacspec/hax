module Core_models.Ops.Try_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::FromResidual`]
class t_FromResidual (v_Self: Type0) (v_R: Type0) = {
  f_from_residual_pre:v_R -> Type0;
  f_from_residual_post:v_R -> v_Self -> Type0;
  f_from_residual:x0: v_R
    -> Prims.Pure v_Self (f_from_residual_pre x0) (fun result -> f_from_residual_post x0 result)
}

/// See [`std::ops::Yeet`]
type t_Yeet (v_T: Type0) = | Yeet : v_T -> t_Yeet v_T

/// See [`std::ops::Try`]
class t_Try (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Residual:Type0;
  f_from_output_pre:f_Output -> Type0;
  f_from_output_post:f_Output -> v_Self -> Type0;
  f_from_output:x0: f_Output
    -> Prims.Pure v_Self (f_from_output_pre x0) (fun result -> f_from_output_post x0 result);
  f_branch_pre:v_Self -> Type0;
  f_branch_post:v_Self -> Core_models.Ops.Control_flow.t_ControlFlow f_Residual f_Output -> Type0;
  f_branch:x0: v_Self
    -> Prims.Pure (Core_models.Ops.Control_flow.t_ControlFlow f_Residual f_Output)
        (f_branch_pre x0)
        (fun result -> f_branch_post x0 result)
}

/// See [`std::ops::Residual`]
class t_Residual (v_Self: Type0) (v_O: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_TryType:Type0;
  f_TryType_i0:t_Try f_TryType
}
