import CoreModels.Core.Funs
import CoreModels.Alloc.Funs

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM

set_option mvcgen.warning false

@[spec]
theorem core.IteratorRange.next_CoreIterRangeStep_spec {Q} (range : core.ops.range.Range Std.Usize)
      (h_lt : (h : range.start.val < range.end.val) →
        ∀ (s : Usize), s.val = range.start.val + 1 →
        PostCond.ok Q (some range.start, { start := s, «end» := range.end }))
      (h_ge : range.start.val ≥ range.end.val → PostCond.ok Q (none, range)) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep range
    ⦃ Q ⦄ := by
  mvcgen [core.IteratorRange.next, core.Usize.Insts.CoreIterRangeStep, uncurry,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
    core.Usize.Insts.CoreCloneClone.clone, core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize]
    <;> grind [UScalar.overflowing_add, BitVec.uaddOverflow, UScalar.overflowing_add_eq]

end CoreModels
