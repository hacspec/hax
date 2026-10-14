module
public import Aeneas
public import CoreModels.Core.TypesPrologue
public import CoreModels.Core.Types
public import Hax.MissingAeneas

@[expose] public section

/-!
# Model of `hax_lib::prop`
-/

open Aeneas.Std
open Aeneas.Std.RustM

namespace hax_lib

/-! ## `impl ToProp for bool` -/

namespace Bool.Insts

@[spec] def Hax_libPropToProp.to_prop (b : Bool) : RustM Prop :=
  ok (b = true)

@[spec] def Hax_libAbstractionAbstractionProp.lift (b : Bool) : RustM Prop :=
  ok (b = true)

end Bool.Insts

namespace prop

/-- Model of `hax_lib::prop::Prop` is Lean's `Prop`. -/
abbrev «Prop» : Type := Prop

/-! ## Monomorphic constructors (`hax_lib::prop::constructors`) -/
namespace constructors

@[spec] def from_bool (b : Bool) : RustM Prop := ok (b = true)
@[spec] def and (lhs other : Prop) : RustM Prop := ok (lhs ∧ other)
@[spec] def or (lhs other : Prop) : RustM Prop := ok (lhs ∨ other)
@[spec] def not (lhs : Prop) : RustM Prop := ok (¬ lhs)
@[spec] def implies (lhs other : Prop) : RustM Prop := ok (lhs → other)
@[spec] def eq {T : Type} (lhs rhs : T) : RustM Prop := ok (lhs = rhs)
@[spec] def ne {T : Type} (lhs rhs : T) : RustM Prop := ok (lhs ≠ rhs)

@[spec] def «forall» {A F : Type} (fn : CoreModels.core.ops.function.Fn F A Prop) (f : F) :
    RustM Prop :=
  ok (∀ a : A, (fn.call f a).holds)

@[spec] def «exists» {A F : Type} (fn : CoreModels.core.ops.function.Fn F A Prop) (f : F) :
    RustM Prop :=
  ok (∃ a : A, (fn.call f a).holds)

end constructors

/-! ## `impl Prop` methods -/
namespace «Prop»

@[spec] def from_bool (b : Bool) : RustM Prop := ok (b = true)

@[spec] def and {B : Type} (inst : CoreModels.core.convert.Into B Prop)
    (self : Prop) (other : B) : RustM Prop := do
  let o ← inst.into other
  ok (self ∧ o)

@[spec] def or {B : Type} (inst : CoreModels.core.convert.Into B Prop)
    (self : Prop) (other : B) : RustM Prop := do
  let o ← inst.into other
  ok (self ∨ o)

@[spec] def not (self : Prop) : RustM Prop :=
  ok (¬ self)

/-- Logical equality of two propositions (modelled as `↔`). -/
@[spec] def eq {B : Type} (inst : CoreModels.core.convert.Into B Prop)
    (self : Prop) (other : B) : RustM Prop := do
  let o ← inst.into other
  ok (self ↔ o)

/-- Logical inequality of two propositions. -/
@[spec] def ne {B : Type} (inst : CoreModels.core.convert.Into B Prop)
    (self : Prop) (other : B) : RustM Prop := do
  let o ← inst.into other
  ok (¬ (self ↔ o))

@[spec] def implies {B : Type} (inst : CoreModels.core.convert.Into B Prop)
    (self : Prop) (other : B) : RustM Prop := do
  let o ← inst.into other
  ok (self → o)

namespace Insts

/-- `impl From<bool> for Prop`. -/
@[spec] def CoreConvertFromBool : CoreModels.core.convert.From Prop Bool :=
  { «from» := fun b => ok (b = true) }

/-- `impl BitAnd<T: Into<Prop>> for Prop` (the `&` operator). -/
@[spec] def CoreOpsBitBitAndTProp.bitand {T : Type} (inst : CoreModels.core.convert.Into T Prop)
    (self : Prop) (other : T) : RustM Prop := do
  let o ← inst.into other
  ok (self ∧ o)

/-- `impl BitOr<T: Into<Prop>> for Prop` (the `|` operator). -/
@[spec] def CoreOpsBitBitOrTProp.bitor {T : Type} (inst : CoreModels.core.convert.Into T Prop)
    (self : Prop) (other : T) : RustM Prop := do
  let o ← inst.into other
  ok (self ∨ o)

/-- `impl Not for Prop` (the `!` operator). -/
@[spec] def CoreOpsBitNotProp.not (self : Prop) : RustM Prop := ok (¬ self)

end Insts

end «Prop»

/-! ## Free functions of `hax_lib::prop` -/

@[spec] def implies {A B : Type} (instA : CoreModels.core.convert.Into A Prop)
    (instB : CoreModels.core.convert.Into B Prop) (a : A) (b : B) : RustM Prop := do
  let pa ← instA.into a
  let pb ← instB.into b
  ok (pa → pb)

@[spec] def «forall» {T U F : Type} (inst : CoreModels.core.convert.Into U Prop)
    (fn : CoreModels.core.ops.function.Fn F T U) (f : F) : RustM Prop :=
  ok (∀ t : T, RustM.holds (do let u ← fn.call f t; inst.into u))

@[spec] def «exists» {T U F : Type} (inst : CoreModels.core.convert.Into U Prop)
    (fn : CoreModels.core.ops.function.Fn F T U) (f : F) : RustM Prop :=
  ok (∃ t : T, RustM.holds (do let u ← fn.call f t; inst.into u))

end prop
end hax_lib
