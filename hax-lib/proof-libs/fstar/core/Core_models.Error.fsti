module Core_models.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::error::Error`]
class t_Error (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Fmt.t_Display v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i1:Core_models.Fmt.t_Debug v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Error v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Error v_Self|} -> i._super_i1

class t_ErrorDefaults (v_Self: Type0) = {
  f_description_pre:v_Self -> Type0;
  f_description_post:v_Self -> string -> Type0;
  f_description:x0: v_Self
    -> Prims.Pure string (f_description_pre x0) (fun result -> f_description_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (#v_T: Type0) {| i0: t_Error v_T |} : t_ErrorDefaults v_T
