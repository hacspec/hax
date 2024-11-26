module Core.Base.Spec.Haxint
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_HaxInt = { f_v:Alloc.Borrow.t_Cow (t_Slice u8) }

let v_HaxInt_ONE: t_HaxInt =
  {
    f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [1uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  t_HaxInt

let v_HaxInt_TWO: t_HaxInt =
  {
    f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [2uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  t_HaxInt

let v_HaxInt_ZERO: t_HaxInt =
  {
    f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list:Prims.list u8 = [] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
        Rust_primitives.Hax.array_of_list 0 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  t_HaxInt

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Clone.t_Clone t_HaxInt =
  {
    f_clone_pre = (fun (self: t_HaxInt) -> true);
    f_clone_post = (fun (self: t_HaxInt) (out: t_HaxInt) -> true);
    f_clone
    =
    fun (self: t_HaxInt) ->
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

let div2 (s: t_HaxInt) : t_HaxInt =
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

let is_zero (s: t_HaxInt) : bool =
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
