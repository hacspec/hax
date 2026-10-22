
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


namespace new_tests.legacy__tombstones__lib

@[spec]
def clean_add (a : u8) (b : u8) : RustM u8 := do (a +? b)

class Speak.AssociatedTypes (Self : Type) where

class Speak (Self : Type)
  [associatedTypes : outParam (Speak.AssociatedTypes (Self : Type))]
  where
  hello (Self) : (Self -> RustM u8)

structure Cat where
  -- no fields

@[spec]
def Impl.hello_hoisted (self : Cat) : RustM u8 := do (pure (1 : u8))

@[reducible] instance Impl.AssociatedTypes : Speak.AssociatedTypes Cat where

instance Impl : Speak Cat where
  hello := (Impl.hello_hoisted)

--  @fail(extraction): ssprove(HAX0008), proverif(HAX0008), coq(HAX0008)
-- [hax::excluded] dyn_in_sig — Unsupported `dyn` traits

--  @fail(extraction): proverif(HAX0008, HAX0008, HAX0008), coq(HAX0008, HAX0008, HAX0008), ssprove(HAX0008, HAX0008, HAX0008)
@[spec]
def dyn_in_body (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  let c : Cat := Cat.mk;
  let d : sorry /- [hax::opaque] Unsupported `dyn` traits -/ ←
    (rust_primitives.unsize c);
  (Speak.hello sorry /- [hax::opaque] Unsupported `dyn` traits -/ d)

--  @fail(extraction): coq(HAX0010, HAX0003), ssprove(HAX0003, HAX0010), legacy-lean(HAX0010, HAX0003), fstar(HAX0010, HAX0003), proverif(HAX0010, HAX0003)
-- [hax::excluded] mut_ref_return — The mutation of this &mut is not allowed here.

--  @fail(extraction): proverif(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), legacy-lean(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), ssprove(HAX0003, HAX0003, HAX0003, HAX0010, HAX0010, HAX0010), coq(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), fstar(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003)
@[spec]
def body_split (buf : (RustSlice u8)) : RustM u8 := do
  (pure
  sorry /- [hax::opaque] The mutation of this &mut is not allowed here. -/)

end new_tests.legacy__tombstones__lib

