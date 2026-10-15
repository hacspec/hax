import CoreModels.Spec.RustPrimitives.Slice

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM

set_option mvcgen.warning false

attribute [spec]
  core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut

@[spec]
theorem core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = core.result.Result.Ok
                     (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  mvcgen [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
    core.slice.Slice.len]
  · grind [UScalar.val]
  · rename_i a hapost
    congr
    apply Subtype.ext
    apply List.ext_getElem
    · rw [a.property]; exact hlen.symm
    · intro i h1 h2
      apply triple_in_hypothesis _ (hapost i (a.property ▸ h1))
      mvcgen; grind [UScalar.val, Array.make]
  · grind

end CoreModels
