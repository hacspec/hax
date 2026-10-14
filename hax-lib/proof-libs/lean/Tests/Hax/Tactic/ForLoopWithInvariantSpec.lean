module
public import Hax

@[expose] public section

/-! # Tests for `Hax.Tactic.ForLoopWithInvariantSpec` -/

set_option mvcgen.warning false

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
open Std.Tactic

namespace Hax.Tests

/-! ## End-to-end signed test

A concrete `for i in (0 : i32) .. 5` loop with invariant `acc.val = 0`, proven through
the signed `forLoopWithInvariant_spec`; no extraction involved. -/

example :
    ⦃ ⌜ True ⌝ ⦄
    Hax.forLoopWithInvariant core.I32.Insts.CoreIterRangeStep
      (fun (_ : I32) (acc : I32) => (ok (acc.val = 0) : RustM Prop))
      (fun (_ : I32) (acc : I32) => (ok acc : RustM I32))
      { start := (0#i32), «end» := (5#i32) } (0#i32)
    ⦃ ⇓ r => ⌜ (ok (r.val = 0) : RustM Prop).holds ⌝ ⦄ := by
  refine forLoopWithInvariant_spec
    (fun _ acc => ok acc) (0#i32) (0#i32) (5#i32)
    (fun _ acc => ok (acc.val = 0)) (by scalar_tac) ?_ ?_
  · -- h_init : `(inv 0 0).holds`, i.e. `(0 : I32).val = 0`
    simp [RustM.holds, Triple, WP.wp, PredTrans.apply]
  · -- h_step : the identity body preserves `acc.val = 0`
    intro acc i _ _ hinv
    have hacc : acc.val = 0 := by
      simpa [RustM.holds, Triple, WP.wp, PredTrans.apply] using hinv
    simp [Triple, WP.wp, PredTrans.apply, RustM.holds, hacc]

end Hax.Tests
