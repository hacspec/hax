
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__yield

--  @fail(extraction): fstar(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), legacy-lean(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), coq(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), ssprove(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001), proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure
  sorry /- [hax::opaque] something is not implemented yet. Got type `Coroutine`: coroutines are not supported by hax -/)

end new_tests.rustc_coverage__yield

