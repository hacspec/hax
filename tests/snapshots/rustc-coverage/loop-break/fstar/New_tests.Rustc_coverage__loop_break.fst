module New_tests.Rustc_coverage__loop_break
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): legacy-lean(HAX0001), fstar(HAX0001), coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
    "",
  ()
  <:
  (Prims.unit & Prims.unit)
