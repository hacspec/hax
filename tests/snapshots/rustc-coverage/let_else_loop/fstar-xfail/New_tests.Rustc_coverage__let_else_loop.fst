module New_tests.Rustc_coverage__let_else_loop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): fstar(HAX0001), legacy-lean(HAX0001), coq(HAX0001), proverif(HAX0008)
let loopy (cond: bool) : Prims.unit =
  match cond <: bool with
  | true -> ()
  | _ ->
    Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
      "",
    ()
    <:
    (Prims.unit & Prims.unit)

/// @fail(extraction): fstar(HAX0001, HAX0001), legacy-lean(HAX0001, HAX0001), coq(HAX0001, HAX0001), proverif(HAX0008, HAX0008)
let e_loop_either_way (cond: bool) : Prims.unit =
  match cond <: bool with
  | true ->
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
            ""
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))
  | _ ->
    Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
      "",
    ()
    <:
    (Prims.unit & Prims.unit)

/// @fail(extraction): proverif(HAX0008, HAX0008), legacy-lean(HAX0001, HAX0001), fstar(HAX0001, HAX0001), coq(HAX0001, HAX0001)
let e_if (cond: bool) : Prims.unit =
  if cond
  then
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
            ""
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))
  else
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
            ""
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = loopy true in
  ()
