module
public import CoreModels.Core.Funs
public import CoreModels.MissingAeneas

@[expose] public section

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM ScalarElab

set_option mvcgen.warning false

/-! # Specs for `rust_primitives::arithmetic` -/

/-! ## `pow` -/

theorem upow_partialSpec {ty : UScalarTy} (x : UScalar ty) (n : Std.U32) :
    partialSpec (UScalar.tryMk ty (x.val ^ n.val))
      (fun r => r.val = x.val ^ n.val ∧ UScalar.inBounds ty (x.val ^ n.val))
      (fun | .panic => ¬ UScalar.inBounds ty (x.val ^ n.val) | _ => False)
      False := by
  grind [UScalar.tryMk, RustM.ofOption, UScalar.tryMkOpt_eq]

theorem ipow_partialSpec {ty : IScalarTy} (x : IScalar ty) (n : Std.U32) :
    partialSpec (IScalar.tryMk ty (x.val ^ n.val))
      (fun r => r.val = x.val ^ n.val ∧ IScalar.inBounds ty (x.val ^ n.val))
      (fun | .panic => ¬ IScalar.inBounds ty (x.val ^ n.val) | _ => False)
      False := by
  grind [IScalar.tryMk, RustM.ofOption, IScalar.tryMkOpt_eq]

/-! `'S` spells the model name up to case (`pow_'S ~> pow_U8`) and `%ToLowerCase`
lowercases it to the Rust spelling (`pow_u8`). -/

uscalar @[step] theorem rust_primitives.arithmetic.«%S».pow_spec (x : «%S») (n : Std.U32) :
    partialSpec ((%ToLowerCase rust_primitives.arithmetic.«pow_'S») x n)
      (fun r => r.val = x.val ^ n.val ∧ x.val ^ n.val ≤ «%S».max)
      (fun | .panic => x.val ^ n.val > «%S».max | _ => False)
      False := by
  simp only [«%S».max_def, «%S».numBits_def]
  convert upow_partialSpec x n using 2
  · rfl
  · grind
  · grind

iscalar @[step] theorem rust_primitives.arithmetic.«%S».pow_spec (x : «%S») (n : Std.U32) :
    partialSpec ((%ToLowerCase rust_primitives.arithmetic.«pow_'S») x n)
      (fun r => r.val = x.val ^ n.val ∧ «%S».min ≤ x.val ^ n.val ∧ x.val ^ n.val ≤ «%S».max)
      (fun | .panic => x.val ^ n.val < «%S».min ∨ x.val ^ n.val > «%S».max
           | _ => False)
      False := by
  simp only [«%S».max_def, «%S».min_def, «%S».numBits_def]
  convert ipow_partialSpec x n using 2
  · rfl
  · grind
  · grind

end CoreModels
