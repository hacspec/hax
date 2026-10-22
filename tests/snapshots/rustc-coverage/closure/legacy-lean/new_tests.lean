
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


namespace new_tests.rustc_coverage__closure

--  @fail(extraction): coq(HAX0006, HAX0003), proverif(HAX0006, HAX0003), fstar(HAX0006, HAX0003), ssprove(HAX0006, HAX0003), legacy-lean(HAX0003, HAX0006)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure
  sorry /- [hax::opaque] The bindings ["countdown"] cannot be mutated here: they don't belong to the closure scope, and this is not allowed. -/)

end new_tests.rustc_coverage__closure

