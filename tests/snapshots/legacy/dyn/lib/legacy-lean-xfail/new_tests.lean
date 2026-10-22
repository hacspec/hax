
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


namespace new_tests.legacy__dyn__lib

class Printable.AssociatedTypes (Self : Type) (S : Type) where

class Printable (Self : Type) (S : Type)
  [associatedTypes : outParam (Printable.AssociatedTypes (Self : Type) (S :
      Type))]
  where
  stringify (Self) (S) : (Self -> RustM S)

@[spec]
def Impl.stringify_hoisted (self : i32) : RustM alloc.string.String := do
  (alloc.string.ToString.to_string i32 self)

@[reducible] instance Impl.AssociatedTypes :
  Printable.AssociatedTypes i32 alloc.string.String
  where

instance Impl : Printable i32 alloc.string.String where
  stringify := (Impl.stringify_hoisted)

--  @fail(extraction): proverif(HAX0008), ssprove(HAX0008), coq(HAX0008)
-- [hax::excluded] print — Unsupported `dyn` traits

end new_tests.legacy__dyn__lib

