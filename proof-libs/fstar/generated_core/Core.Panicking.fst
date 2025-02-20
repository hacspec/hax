module Core.Panicking
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_AssertKind =
  | AssertKind_Eq : t_AssertKind
  | AssertKind_Ne : t_AssertKind
  | AssertKind_Match : t_AssertKind

let t_AssertKind_cast_to_repr (x: t_AssertKind) : isize =
  match x with
  | AssertKind_Eq  -> isz 0
  | AssertKind_Ne  -> isz 1
  | AssertKind_Match  -> isz 3

type t_Never =

let t_Never_cast_to_repr (x: t_Never) : Rust_primitives.Hax.t_Never = match x with

let never_to_any (#v_T: Type0) (x: t_Never) : v_T = Rust_primitives.Hax.never_to_any (match x with )

let rec panic_fmt (fmt: Core.Fmt.t_Arguments) : Rust_primitives.Hax.t_Never = panic_fmt fmt

/// The underlying implementation of core's `panic!` macro when no formatting is used.
let panic (expr: string) : Rust_primitives.Hax.t_Never =
  panic_fmt (Core.Fmt.impl_2__new_const (sz 1)
        (let list = [expr] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
      <:
      Core.Fmt.t_Arguments)

let panic_display
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Display v_T)
      (x: v_T)
    : Rust_primitives.Hax.t_Never =
  panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
        (sz 1)
        (let list = [""] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        (let list = [Core.Fmt.Rt.impl_1__new_display #v_T x <: Core.Fmt.Rt.t_Argument] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
      <:
      Core.Fmt.t_Arguments)

let panic_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  panic_display #string "explicit panic"
