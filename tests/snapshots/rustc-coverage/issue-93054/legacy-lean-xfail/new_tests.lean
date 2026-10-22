
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


namespace new_tests.rustc_coverage__issue_93054

inductive Never : Type


@[spec]
def Never_cast_to_repr (x : Never) : RustM rust_primitives.hax.Never := do
  match x with 

@[spec]
def Impl.bar (self : Never) : RustM rust_primitives.hax.Tuple0 := do
  (rust_primitives.hax.never_to_any (← match self with ))

--  @fail(extraction): fstar(HAX0001), ssprove(HAX0001), legacy-lean(HAX0001), coq(HAX0001)
--  @fail(extraction): proverif(HAX0001)
-- [hax::excluded] foo2 — something is not implemented yet. Got type `Coroutine`: coroutines are not supported by hax

@[spec]
def make (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.option.Option Never) := do
  (pure core_models.option.Option.None)

@[spec]
def Impl.foo (self : Never) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (rust_primitives.hax.never_to_any (← match self with ));
  (rust_primitives.hax.never_to_any
    (← (core_models.option.Impl.map
      Never
      rust_primitives.hax.Never
      (Never -> RustM rust_primitives.hax.Never)
      (← (make rust_primitives.hax.Tuple0.mk))
      (fun never => (do match never with  : RustM rust_primitives.hax.Never)))))

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__issue_93054

