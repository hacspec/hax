module New_tests.Rustc_coverage__auxiliary__executor
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Dummy "executor" that just repeatedly polls a future until it's ready.
/// @fail(extraction): fstar(HAX0003, HAX0003, HAX0003, HAX0003, HAX0003), ssprove(HAX0003, HAX0003, HAX0003, HAX0003, HAX0008), coq(HAX0008, HAX0003, HAX0003, HAX0003, HAX0003), legacy-lean(HAX0003, HAX0003, HAX0003, HAX0003, HAX0003), proverif(HAX0003, HAX0003, HAX0003, HAX0003, HAX0008)
let block_on
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Future.Future.t_Future v_F)
      (future: v_F)
    : i0.f_Output =
  Rust_primitives.Hax.failure "[hax::opaque] The mutation of this &mut is not allowed here." ""
