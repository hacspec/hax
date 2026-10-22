module New_tests.Rustc_coverage__closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): coq(HAX0006, HAX0003), proverif(HAX0006, HAX0003), fstar(HAX0006, HAX0003), ssprove(HAX0006, HAX0003), legacy-lean(HAX0003, HAX0006)
let main (_: Prims.unit) : Prims.unit =
  Rust_primitives.Hax.failure "[hax::opaque] The bindings [\"countdown\"] cannot be mutated here: they don't belong to the closure scope, and this is not allowed."
    ""
