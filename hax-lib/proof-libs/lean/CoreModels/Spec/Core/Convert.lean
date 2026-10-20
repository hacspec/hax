import CoreModels.Spec.RustPrimitives.Slice

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM

set_option mvcgen.warning false

/- The proof below reads each element through the closure passed to `array::from_fn`. -/
attribute [local spec]
  core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut

/-- `<[T; N]>::try_from(s)` succeeds exactly when `s` has length `N`.

`[Inhabited T]` is needed by the `array::from_fn` spec this proof goes through. -/
@[spec]
theorem core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = if hlen : s.val.length = N.val
                   then core.result.Result.Ok (Std.Array.make N s.val (by simp [hlen]))
                   else core.result.Result.Err () ⌝ ⦄ := by
  mvcgen [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
    core.slice.Slice.len]
  · grind [UScalar.val]
  · rename_i _ a hapost
    have hlen : s.val.length = N.val := by grind [Slice.len_val, UScalar.eq_equiv]
    rw [dif_pos hlen]
    congr
    apply Subtype.ext
    apply List.ext_getElem
    · rw [a.property]; exact hlen.symm
    · intro i h1 h2
      apply triple_in_hypothesis _ (hapost i (a.property ▸ h1))
      mvcgen; grind [UScalar.val, Array.make]
  · grind [Slice.len_val, UScalar.eq_equiv]

end CoreModels
