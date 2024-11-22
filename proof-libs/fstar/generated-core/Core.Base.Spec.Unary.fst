module Core.Base.Spec.Unary
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Unary = | Unary : Core.Base.Spec.Haxint.t_HaxInt -> t_Unary

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Clone.t_Clone t_Unary =
  {
    f_clone_pre = (fun (self: t_Unary) -> true);
    f_clone_post = (fun (self: t_Unary) (out: t_Unary) -> true);
    f_clone
    =
    fun (self: t_Unary) ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
                (sz 0)
                (let list = ["not yet implemented: specification needed"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
                (Core.Fmt.Rt.impl_1__none () <: t_Array Core.Fmt.Rt.t_Argument (sz 0))
              <:
              Core.Fmt.t_Arguments)
          <:
          Rust_primitives.Hax.t_Never)
  }

type t_UNARY =
  | UNARY_ZERO : t_UNARY
  | UNARY_SUCC : t_Unary -> t_UNARY

let pred (x: t_Unary) : t_Unary =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
            (sz 0)
            (let list = ["not yet implemented: specification needed"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            (Core.Fmt.Rt.impl_1__none () <: t_Array Core.Fmt.Rt.t_Argument (sz 0))
          <:
          Core.Fmt.t_Arguments)
      <:
      Rust_primitives.Hax.t_Never)

let succ (x: t_Unary) : t_Unary =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
            (sz 0)
            (let list = ["not yet implemented: specification needed"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            (Core.Fmt.Rt.impl_1__none () <: t_Array Core.Fmt.Rt.t_Argument (sz 0))
          <:
          Core.Fmt.t_Arguments)
      <:
      Rust_primitives.Hax.t_Never)

let unary_from_int (x: Core.Base.Spec.Haxint.t_HaxInt) : t_Unary = Unary x <: t_Unary

let unary_to_int (s: t_Unary) : Core.Base.Spec.Haxint.t_HaxInt = s._0

let match_unary (s: t_Unary) : t_UNARY =
  if
    Core.Base.Spec.Haxint.is_zero (unary_to_int (Core.Clone.f_clone #t_Unary
              #FStar.Tactics.Typeclasses.solve
              s
            <:
            t_Unary)
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  then UNARY_ZERO <: t_UNARY
  else UNARY_SUCC (pred s) <: t_UNARY
