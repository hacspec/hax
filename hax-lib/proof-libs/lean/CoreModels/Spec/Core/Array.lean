import CoreModels.Core.Funs
import CoreModels.Spec.Core.Slice
import CoreModels.Spec.RustPrimitives.Slice

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM
set_option mvcgen.warning false

open ScalarElab

uscalar @[spec] theorem «%S».Array.eq_spec {N : Std.Usize} {Q}
  (a : Array «%S» N) (b : Array «%S» N) (h : PostCond.ok Q (a.val == b.val)) :
  ⦃ ⌜ True ⌝ ⦄
  core.Array.Insts.CoreCmpPartialEqArray.eq core.«%S».Insts.CoreCmpPartialEq'S a b
  ⦃ Q ⦄ := by
  mvcgen -trivial [core.Array.Insts.CoreCmpPartialEqArray.eq,
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop,
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body, rust_primitives.slice.array_index,
    core.«%S».Insts.CoreCmpPartialEq'S]
  case vc1.γ => exact Nat
  case vc4.termination => exact fun i => N.val - i.val
  case vc3.rel => exact (· < ·)
  case vc5.hwf => exact wellFounded_lt
  case vc2.inv => exact fun i => a.val.take i.val = b.val.take i.val
  case vc7.hQ =>
    constructor
    · simp_all [@List.take_add, @List.take_one, -List.take_append_getElem]
    · grind
  case vc9.hQ => convert h; grind
  case vc12.hQ => convert h; grind [List.take_eq_self_iff, List.Vector.length_val]
  all_goals grind

@[spec]
theorem Array.index_range_spec
      {T : Type} {N : Std.Usize} (arr : Std.Array T N)
      (r : core.ops.range.Range Std.Usize)
      (h0 : r.start.val ≤  r.end.val)
      (h1 : r.end.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Shared0Slice.Insts.CoreOpsIndexIndexRangeUsizeSlice T)
      arr r
    ⦃ ⇓ r' => ⌜ r'.val = arr.val.slice r.start.val r.end.val ∧
                r'.val.length + r.start.val = r.end.val ⌝ ⦄ := by
  mvcgen [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice]
    <;> grind

attribute [spec] core.array.from_fn

end CoreModels
