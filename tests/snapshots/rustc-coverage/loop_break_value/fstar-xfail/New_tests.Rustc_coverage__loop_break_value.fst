module New_tests.Rustc_coverage__loop_break_value
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): fstar(HAX0001), proverif(HAX0008), ssprove(HAX0001), coq(HAX0001, HAX0001), legacy-lean(HAX0001)
let main (_: Prims.unit) : Prims.unit =
  let result:i32 =
    Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
      "",
    ()
    <:
    (Prims.unit & Prims.unit)
  in
  ()
