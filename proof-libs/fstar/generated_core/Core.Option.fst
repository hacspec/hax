module Core.Option
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Option (v_T: Type0) =
  | Option_None : t_Option v_T
  | Option_Some : v_T -> t_Option v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Option v_T) =
  {
    f_clone_pre = (fun (self: t_Option v_T) -> true);
    f_clone_post = (fun (self: t_Option v_T) (out: t_Option v_T) -> true);
    f_clone
    =
    fun (self: t_Option v_T) ->
      match self with
      | Option_Some x ->
        Option_Some (Core.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve x) <: t_Option v_T
      | Option_None  -> Option_None <: t_Option v_T
  }

let impl_1__is_some (#v_T: Type0) (self: t_Option v_T) : bool =
  match self with
  | Option_Some _ -> true
  | _ -> false

let unwrap_failed (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic "called `Option::unwrap()` on a `None` value"

let impl_1__unwrap (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure v_T (requires impl_1__is_some #v_T self___) (fun _ -> Prims.l_True) =
  match self with
  | Option_Some v_val -> v_val
  | Option_None  ->
    Rust_primitives.Hax.never_to_any (unwrap_failed () <: Rust_primitives.Hax.t_Never)

let expect_failed (msg: string) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_display #string msg

let impl_1__expect (#v_T: Type0) (self: t_Option v_T) (msg: string) : v_T =
  match self with
  | Option_Some v_val -> v_val
  | Option_None  ->
    Rust_primitives.Hax.never_to_any (expect_failed msg <: Rust_primitives.Hax.t_Never)
