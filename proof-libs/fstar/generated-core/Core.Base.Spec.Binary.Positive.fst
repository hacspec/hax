module Core.Base.Spec.Binary.Positive
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Positive = | Positive : Core.Base.Spec.Haxint.t_HaxInt -> t_Positive

type t_POSITIVE =
  | POSITIVE_XH : t_POSITIVE
  | POSITIVE_XO : t_Positive -> t_POSITIVE
  | POSITIVE_XI : t_Positive -> t_POSITIVE

let positive_from_int (x: Core.Base.Spec.Haxint.t_HaxInt) : t_Positive = Positive x <: t_Positive

let positive_to_int (s: t_Positive) : Core.Base.Spec.Haxint.t_HaxInt = s._0

let xH: t_Positive = Positive Core.Base.Spec.Haxint.v_HaxInt_ONE <: t_Positive

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Clone.t_Clone t_Positive =
  {
    f_clone_pre = (fun (self: t_Positive) -> true);
    f_clone_post = (fun (self: t_Positive) (out: t_Positive) -> true);
    f_clone
    =
    fun (self: t_Positive) ->
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

let match_positive__is_xH (s: t_Positive) : bool =
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

let match_positive__is_xI (s: t_Positive) : bool =
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

let match_positive__is_xO (s: t_Positive) : bool =
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

let xI (s: t_Positive) : t_Positive =
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

let xO (s: t_Positive) : t_Positive =
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

let match_positive (s: t_Positive) : t_POSITIVE =
  if
    match_positive__is_xH (Core.Clone.f_clone #t_Positive #FStar.Tactics.Typeclasses.solve s
        <:
        t_Positive)
  then POSITIVE_XH <: t_POSITIVE
  else
    if
      match_positive__is_xO (Core.Clone.f_clone #t_Positive #FStar.Tactics.Typeclasses.solve s
          <:
          t_Positive)
    then
      POSITIVE_XO
      (positive_from_int (Core.Base.Spec.Haxint.div2 (positive_to_int s
                <:
                Core.Base.Spec.Haxint.t_HaxInt)
            <:
            Core.Base.Spec.Haxint.t_HaxInt))
      <:
      t_POSITIVE
    else
      POSITIVE_XI
      (positive_from_int (Core.Base.Spec.Haxint.div2 (positive_to_int s
                <:
                Core.Base.Spec.Haxint.t_HaxInt)
            <:
            Core.Base.Spec.Haxint.t_HaxInt))
      <:
      t_POSITIVE
