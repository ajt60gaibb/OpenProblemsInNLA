/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical counterexample: Matthew J. Colbrook.
AI-assisted exact algebra following the independently reviewed statement freeze.
-/
import NLA.TR27.Definitions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27

/-- Exact pointwise identity underlying the integral-image construction. -/
theorem integral_quadratic (w : ParameterSpace) :
    85 * (w 0 ^ 12) ^ 2 +
      (8 * homogeneousMap w 0 + 9 * homogeneousMap w 1) * w 0 ^ 12 -
      5 * (homogeneousMap w 0) ^ 2 = 0 := by
  norm_num [homogeneousMap, homogeneousCoordinate, coordinateIndex, powerSum]
  ring

/-- The displayed quotient formula defines an actual complex linear map. -/
def quotientLinearMap : SourceSpace →ₗ[ℂ] Space where
  toFun := quotientMap
  map_add' u v := by
    ext j
    simp only [quotientMap, Pi.add_apply]
    ring
  map_smul' a v := by
    ext j
    simp only [quotientMap, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro v
  refine ⟨![v 0 / 5, 0, v 1 / 5, v 2 / 5, v 3 / 5, v 4 / 5,
    v 5 / 5, v 6 / 5, v 7 / 5, v 8 / 5, v 9 / 5, v 10 / 5, v 11 / 5], ?_⟩
  ext j
  fin_cases j <;> norm_num [quotientMap, coordinateIndex, Fin.isValue, Fin.ext_iff, Matrix.cons_val_two] <;> ring!

theorem quotientMap_center : quotientMap center = 0 := by
  ext j
  fin_cases j <;>
    norm_num [quotientMap, center, coordinateIndex, sourceUnit, sourceCurve, powerSum, Fin.isValue, Fin.ext_iff]

theorem quotientMap_kernel :
    {w : SourceSpace | quotientMap w = 0} = Submodule.span ℂ {center} := by
  ext w
  change quotientMap w = 0 ↔ w ∈ Submodule.span ℂ {center}
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hw
    refine ⟨-w 1 / 5, ?_⟩
    ext i
    fin_cases i
    · have h := congrFun hw 0
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
    · have h := congrFun hw 1
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 2
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 3
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 4
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 5
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 6
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 7
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 8
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 9
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 10
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
    · have h := congrFun hw 11
      norm_num [quotientMap, coordinateIndex, powerSum, Fin.isValue, Fin.ext_iff] at h
      norm_num [center, sourceUnit, sourceCurve, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.ext_iff]
      linear_combination (norm := ring!) -(1 / 5 : ℂ) * h
  · rintro ⟨a, rfl⟩
    change quotientLinearMap (a • center) = 0
    rw [map_smul]
    change a • quotientMap center = 0
    rw [quotientMap_center, smul_zero]

/-- The frozen quotient statement, with no geometric or rank assumptions. -/
theorem quotient_semantics :
    (∃ P : SourceSpace →ₗ[ℂ] Space, (P : SourceSpace → Space) = quotientMap) ∧
    Function.Surjective quotientMap ∧
    {w : SourceSpace | quotientMap w = 0} = Submodule.span ℂ {center} := by
  exact ⟨⟨quotientLinearMap, rfl⟩, quotientMap_surjective, quotientMap_kernel⟩

/-- The quotient deletes precisely the source coordinate numbered one. -/
theorem coordinateIndex_ne_one (j : Fin 12) : coordinateIndex j ≠ 1 := by
  fin_cases j <;> decide

theorem witnessVector_apply (j : Fin 12) :
    witnessVector j = -powerSum (coordinateIndex j : ℕ) := by
  simp [witnessVector, quotientMap, sourceUnit, Ne.symm (coordinateIndex_ne_one j)]

theorem curve_some_apply (t : ℂ) (j : Fin 12) :
    curve (some t) j = 5 * t ^ (coordinateIndex j : ℕ) -
      powerSum (coordinateIndex j : ℕ) * t := by
  simp [curve, quotientMap, sourceCurve]

theorem homogeneousMap_apply (w : ParameterSpace) (j : Fin 12) :
    homogeneousMap w j =
      5 * w 0 ^ (12 - (coordinateIndex j : ℕ)) * w 1 ^ (coordinateIndex j : ℕ) -
      powerSum (coordinateIndex j : ℕ) * w 0 ^ 11 * w 1 := by
  simp [homogeneousMap, homogeneousCoordinate]

/-- The finite chart is the same exact curve used by the rank construction. -/
theorem homogeneousMap_one (t : ℂ) : homogeneousMap ![1, t] = curve (some t) := by
  ext j
  simp [homogeneousMap_apply, curve_some_apply]

/-- The homogeneous infinity direction is also included in the actual image. -/
theorem homogeneousMap_infinity : homogeneousMap ![0, 1] = curve none := by
  ext j
  fin_cases j <;>
    norm_num [homogeneousMap_apply, curve, quotientMap, sourceCurve, sourceUnit,
      coordinateIndex, powerSum, Fin.ext_iff, Fin.isValue]

theorem curve_mem_range_homogeneousMap (t : Option ℂ) :
    curve t ∈ Set.range homogeneousMap := by
  cases t with
  | none => exact ⟨![0, 1], homogeneousMap_infinity⟩
  | some t => exact ⟨![1, t], homogeneousMap_one t⟩

/-- The first coordinate certifies that the target vector is nonzero. -/
theorem witnessVector_nonzero : witnessVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [witnessVector_apply, coordinateIndex, powerSum] at h0

/-- All finite parameters and the point at infinity give nonzero vectors. -/
theorem curve_nonzero : ∀ t : Option ℂ, curve t ≠ 0 := by
  rintro (_ | t) h
  · have hlast := congrFun h 11
    norm_num [curve, quotientMap, sourceCurve, sourceUnit, coordinateIndex,
      powerSum, Fin.ext_iff, Fin.isValue] at hlast
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [curve_some_apply, coordinateIndex, powerSum] at h0 h1
    have ht : t = (5 : ℂ) / 3 := by
      linear_combination -(1 / 3 : ℂ) * h0
    rw [ht] at h1
    norm_num at h1

/-- The displayed three-term expression is exact in the quotient space. -/
theorem curve_three_sum :
    curve (some 1) + curve (some 2) + curve (some 3) = witnessVector := by
  have h : quotientLinearMap center = 0 := quotientMap_center
  rw [center, map_sub, map_sub, map_sub] at h
  change witnessVector - curve (some 1) - curve (some 2) - curve (some 3) = 0 at h
  linear_combination -h

theorem borderCurve_zero : borderCurve 0 = witnessVector := by
  ext j
  fin_cases j <;> norm_num [borderCurve, witnessVector_apply, coordinateIndex, powerSum, Fin.ext_iff, Fin.isValue]

theorem borderCurve_nonzero (t : ℂ) : borderCurve t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [borderCurve, coordinateIndex] at h0

theorem borderCurve_divided_difference (t : ℂ) (ht : t ≠ 0) :
    borderCurve t = t⁻¹ • (curve (some t) - curve (some 0)) := by
  ext j
  fin_cases j <;>
    norm_num [borderCurve, curve_some_apply, coordinateIndex, powerSum,
      Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Fin.ext_iff, Fin.isValue] <;>
    field_simp

end NLA.TR27
