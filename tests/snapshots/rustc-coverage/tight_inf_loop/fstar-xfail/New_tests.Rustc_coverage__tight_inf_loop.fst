module New_tests.Rustc_coverage__tight_inf_loop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): legacy-lean(HAX0001), proverif(HAX0008), coq(HAX0001), fstar(HAX0001)
let main (_: Prims.unit) : Prims.unit =
  if false
  then
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
            ""
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))
