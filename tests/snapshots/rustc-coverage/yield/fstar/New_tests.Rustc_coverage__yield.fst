module New_tests.Rustc_coverage__yield
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): fstar(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), legacy-lean(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), coq(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), ssprove(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
let main (_: Prims.unit) : Prims.unit =
  Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Got type `Coroutine`: coroutines are not supported by hax"
    ""
