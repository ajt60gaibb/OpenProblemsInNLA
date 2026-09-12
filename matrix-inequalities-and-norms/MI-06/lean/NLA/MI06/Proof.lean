/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's rational counterexample to MI-06.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI06.Definitions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder Matrix MatrixOrder
noncomputable section

namespace NLA.MI06

theorem modulus_eq_sqrt_proved {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModulus X = CFC.sqrt (X.conjTranspose * X) ∧
    (matrixModulus X).PosSemidef := by
  exact ⟨rfl, Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg X)⟩

private theorem modulus_of_positive_square {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y.PosSemidef) (h : Y * Y = X.conjTranspose * X) :
    matrixModulus X = Y := by
  exact CFC.sqrt_unique h hY.nonneg

private theorem rankOne_posSemidef {n : ℕ} (v : Fin n → ℂ) :
    (rankOne v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

private theorem diagonal_table_posSemidef (a b c : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (!![a, 0, 0; 0, b, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef := by
  have h : (!![a, 0, 0; 0, b, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal ![a, b, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [h]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

private theorem rightModulusA_posSemidef : rightModulusA.PosSemidef := by
  have h : rightModulusA = (1 / 20 : ℂ) • rankOne (![4, 3, 0] : Fin 3 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rightModulusA, rankOne, Matrix.vecMulVec, map_ofNat]
  rw [h]
  exact (rankOne_posSemidef _).smul (by norm_num [Complex.nonneg_iff])

private theorem axialModulus_posSemidef : axialModulus.PosSemidef := by
  exact diagonal_table_posSemidef _ _ _ (by norm_num [Complex.nonneg_iff])
    le_rfl le_rfl

private theorem leftModulusB_posSemidef : leftModulusB.PosSemidef := by
  have h : leftModulusB = (1 / 20 : ℂ) • rankOne (![4, 0, 3] : Fin 3 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [leftModulusB, rankOne, Matrix.vecMulVec, map_ofNat]
  rw [h]
  exact (rankOne_posSemidef _).smul (by norm_num [Complex.nonneg_iff])

private theorem rightModulusSum_posSemidef : rightModulusSum.PosSemidef := by
  exact diagonal_table_posSemidef _ _ _ (by norm_num [Complex.nonneg_iff])
    (by norm_num [Complex.nonneg_iff]) le_rfl

private theorem leftModulusSum_posSemidef : leftModulusSum.PosSemidef := by
  exact diagonal_table_posSemidef _ _ _ (by norm_num [Complex.nonneg_iff])
    le_rfl (by norm_num [Complex.nonneg_iff])

private theorem missingA_posSemidef : missingA.PosSemidef := by
  exact diagonal_table_posSemidef _ _ _ le_rfl le_rfl (by norm_num [Complex.nonneg_iff])

private theorem missingB_posSemidef : missingB.PosSemidef := by
  exact diagonal_table_posSemidef _ _ _ le_rfl (by norm_num [Complex.nonneg_iff]) le_rfl

private theorem modulus_witnessA : matrixModulus witnessA = rightModulusA := by
  apply modulus_of_positive_square _ _ rightModulusA_posSemidef
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, rightModulusA, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem modulus_witnessA_adjoint :
    matrixModulus witnessA.conjTranspose = axialModulus := by
  apply modulus_of_positive_square _ _ axialModulus_posSemidef
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, axialModulus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem modulus_witnessB : matrixModulus witnessB = axialModulus := by
  apply modulus_of_positive_square _ _ axialModulus_posSemidef
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessB, axialModulus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem modulus_witnessB_adjoint :
    matrixModulus witnessB.conjTranspose = leftModulusB := by
  apply modulus_of_positive_square _ _ leftModulusB_posSemidef
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessB, leftModulusB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem modulus_sum :
    matrixModulus (witnessA + witnessB) = rightModulusSum := by
  apply modulus_of_positive_square _ _ rightModulusSum_posSemidef
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, rightModulusSum, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem modulus_sum_adjoint :
    matrixModulus (witnessA + witnessB).conjTranspose = leftModulusSum := by
  apply modulus_of_positive_square _ _ leftModulusSum_posSemidef
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, leftModulusSum, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem symmetricModulus_A : symmetricModulus witnessA = symmetricA := by
  rw [symmetricModulus, modulus_witnessA, modulus_witnessA_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightModulusA, axialModulus, symmetricA]

private theorem symmetricModulus_B : symmetricModulus witnessB = symmetricB := by
  rw [symmetricModulus, modulus_witnessB, modulus_witnessB_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftModulusB, axialModulus, symmetricB]

private theorem symmetricModulus_sum :
    symmetricModulus (witnessA + witnessB) = symmetricSum := by
  rw [symmetricModulus, modulus_sum, modulus_sum_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightModulusSum, leftModulusSum, symmetricSum]

private theorem symmetricA_decomposition :
    symmetricA = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne directionA -
      (1 / 8 : ℂ) • missingA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricA, directionA, missingA, rankOne, Matrix.vecMulVec, Matrix.one_apply, map_ofNat]

private theorem symmetricB_decomposition :
    symmetricB = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne directionB -
      (1 / 8 : ℂ) • missingB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricB, directionB, missingB, rankOne, Matrix.vecMulVec, Matrix.one_apply, map_ofNat]

theorem witness_moduli_proved :
    matrixModulus witnessA = rightModulusA ∧
    matrixModulus witnessA.conjTranspose = axialModulus ∧
    matrixModulus witnessB = axialModulus ∧
    matrixModulus witnessB.conjTranspose = leftModulusB ∧
    matrixModulus (witnessA + witnessB) = rightModulusSum ∧
    matrixModulus (witnessA + witnessB).conjTranspose = leftModulusSum ∧
    symmetricModulus witnessA = symmetricA ∧
    symmetricModulus witnessB = symmetricB ∧
    symmetricModulus (witnessA + witnessB) = symmetricSum ∧
    symmetricA = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne directionA -
      (1 / 8 : ℂ) • missingA ∧
    symmetricB = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne directionB -
      (1 / 8 : ℂ) • missingB := by
  exact ⟨modulus_witnessA, modulus_witnessA_adjoint, modulus_witnessB,
    modulus_witnessB_adjoint, modulus_sum, modulus_sum_adjoint, symmetricModulus_A,
    symmetricModulus_B, symmetricModulus_sum, symmetricA_decomposition,
    symmetricB_decomposition⟩

private theorem squaredLength_pos {n : ℕ} (w : Fin n → ℂ) (hw : w ≠ 0) :
    0 < squaredLength w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  apply Finset.sum_pos'
  · intro j _
    exact Complex.normSq_nonneg (w j)
  · exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

theorem two_vector_orthogonal_proved (a b : Fin 3 → ℂ) :
    ∃ w : Fin 3 → ℂ, 0 < squaredLength w ∧
      star a ⬝ᵥ w = 0 ∧ star b ⬝ᵥ w = 0 := by
  let F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun w => ![star a ⬝ᵥ w, star b ⬝ᵥ w]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [dotProduct_add]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [dotProduct_smul] }
  have hF : ¬ Function.Injective F := by
    intro h
    have hdim := LinearMap.finrank_le_finrank_of_injective h
    norm_num [Module.finrank_fintype_fun_eq_card] at hdim
  obtain ⟨x, hx⟩ := not_forall.mp hF
  obtain ⟨y, hy⟩ := not_forall.mp hx
  obtain ⟨hxy, hne⟩ := Classical.not_imp.mp hy
  have hz : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have ha : star a ⬝ᵥ (x - y) = 0 := congrFun hz (0 : Fin 2)
  have hb : star b ⬝ᵥ (x - y) = 0 := congrFun hz (1 : Fin 2)
  exact ⟨x - y, squaredLength_pos _ (sub_ne_zero.mpr hne), ha, hb⟩

private theorem quadraticForm_add {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → ℂ) :
    quadraticForm (H + K) w = quadraticForm H w + quadraticForm K w := by
  simp [quadraticForm, Matrix.add_mulVec]

private theorem quadraticForm_sub {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → ℂ) :
    quadraticForm (H - K) w = quadraticForm H w - quadraticForm K w := by
  simp [quadraticForm, Matrix.sub_mulVec]

private theorem quadraticForm_smul {n : ℕ} (r : ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (hr : r.im = 0) :
    quadraticForm (r • H) w = r.re * quadraticForm H w := by
  unfold quadraticForm
  rw [Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, Complex.mul_re, hr, zero_mul, sub_zero]

private theorem quadraticForm_one {n : ℕ} (w : Fin n → ℂ) :
    quadraticForm 1 w = squaredLength w := by
  simp [quadraticForm, squaredLength, dotProduct, Complex.normSq_apply, Complex.mul_re]

private theorem quadraticForm_rankOne_zero {n : ℕ} (u w : Fin n → ℂ)
    (h : star u ⬝ᵥ w = 0) : quadraticForm (rankOne u) w = 0 := by
  simp [quadraticForm, rankOne, Matrix.vecMulVec_mulVec, h]

private theorem quadraticForm_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (w : Fin n → ℂ) : 0 ≤ quadraticForm H w := by
  exact (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg w)).1

private theorem quadraticForm_mono {n : ℕ} {H K : Matrix (Fin n) (Fin n) ℂ}
    (h : H ≤ K) (w : Fin n → ℂ) : quadraticForm H w ≤ quadraticForm K w := by
  have hp := quadraticForm_nonneg (K - H) (Matrix.le_iff.mp h) w
  rw [quadraticForm_sub] at hp
  linarith

private theorem unitaryConjugate_add {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H K : Matrix (Fin n) (Fin n) ℂ) :
    unitaryConjugate U (H + K) = unitaryConjugate U H + unitaryConjugate U K := by
  simp [unitaryConjugate, Matrix.mul_add, Matrix.add_mul]

private theorem unitaryConjugate_sub {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H K : Matrix (Fin n) (Fin n) ℂ) :
    unitaryConjugate U (H - K) = unitaryConjugate U H - unitaryConjugate U K := by
  simp [unitaryConjugate, Matrix.mul_sub, Matrix.sub_mul]

private theorem unitaryConjugate_smul {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (r : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    unitaryConjugate U (r • H) = r • unitaryConjugate U H := by
  simp [unitaryConjugate]

private theorem unitaryConjugate_one {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryConjugate U 1 = 1 := by
  change (U : Matrix (Fin n) (Fin n) ℂ) * 1 *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1
  rw [Matrix.mul_one]
  exact U.property.2

private theorem unitaryConjugate_rankOne {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (u : Fin n → ℂ) :
    unitaryConjugate U (rankOne u) =
      rankOne ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) := by
  simp only [unitaryConjugate, rankOne, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

private theorem unitaryConjugate_posSemidef {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) : (unitaryConjugate U H).PosSemidef := by
  exact hH.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℂ)

/-- The rotated rank-one term vanishes; the remaining subtracted PSD term
can only decrease the actual quadratic form. No diagonalization is needed. -/
private theorem upper_bound_of_decomposition {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (H E : Matrix (Fin n) (Fin n) ℂ)
    (u w : Fin n → ℂ) (hE : E.PosSemidef)
    (hH : H = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne u - (1 / 8 : ℂ) • E)
    (horth : star ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) ⬝ᵥ w = 0) :
    quadraticForm (unitaryConjugate U H) w ≤ (1 / 8 : ℝ) * squaredLength w := by
  rw [hH]
  simp only [unitaryConjugate_sub, unitaryConjugate_add, unitaryConjugate_smul,
    unitaryConjugate_one, unitaryConjugate_rankOne, quadraticForm_sub, quadraticForm_add]
  rw [quadraticForm_smul _ _ _ (by norm_num),
    quadraticForm_smul _ _ _ (by norm_num),
    quadraticForm_smul _ _ _ (by norm_num), quadraticForm_one,
    quadraticForm_rankOne_zero _ _ horth]
  have hp := quadraticForm_nonneg _ (unitaryConjugate_posSemidef U E hE) w
  norm_num
  linarith

private theorem symmetricSum_lower_bound : (3 / 8 : ℂ) • 1 ≤ symmetricSum := by
  rw [Matrix.le_iff]
  have h : symmetricSum - (3 / 8 : ℂ) • 1 =
      (!![3 / 8, 0, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [symmetricSum, Matrix.one_apply]
  rw [h]
  exact diagonal_table_posSemidef _ _ _ (by norm_num [Complex.nonneg_iff]) le_rfl le_rfl

theorem witness_quadratic_bounds_proved (U V : Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ w : Fin 3 → ℂ, 0 < squaredLength w ∧
      star ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ directionA) ⬝ᵥ w = 0 ∧
      star ((V : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ directionB) ⬝ᵥ w = 0 ∧
      (3 / 8 : ℝ) * squaredLength w ≤
        quadraticForm (symmetricModulus (witnessA + witnessB)) w ∧
      quadraticForm (unitaryConjugate U (symmetricModulus witnessA)) w ≤
        (1 / 8 : ℝ) * squaredLength w ∧
      quadraticForm (unitaryConjugate V (symmetricModulus witnessB)) w ≤
        (1 / 8 : ℝ) * squaredLength w := by
  obtain ⟨w, hw, ha, hb⟩ := two_vector_orthogonal_proved
    ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ directionA)
    ((V : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ directionB)
  refine ⟨w, hw, ha, hb, ?_, ?_, ?_⟩
  · rw [symmetricModulus_sum]
    have h := quadraticForm_mono symmetricSum_lower_bound w
    rw [quadraticForm_smul _ _ _ (by norm_num), quadraticForm_one] at h
    norm_num at h
    exact h
  · rw [symmetricModulus_A]
    exact upper_bound_of_decomposition U symmetricA missingA directionA w
      missingA_posSemidef symmetricA_decomposition ha
  · rw [symmetricModulus_B]
    exact upper_bound_of_decomposition V symmetricB missingB directionB w
      missingB_posSemidef symmetricB_decomposition hb

/-- The only interval certificate is an exact rational point inequality.
The square-root comparison below consumes this theorem directly. -/
private theorem scalar_squared_gap : (2 : ℝ) < 9 / 4 := by
  interval_decide (trust := kernel)

private theorem sqrt_two_lt_three_halves : Real.sqrt 2 < (3 / 2 : ℝ) := by
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) scalar_squared_gap
  rw [show (9 / 4 : ℝ) = (3 / 2 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  exact h

private theorem scalar_coefficient_gap : Real.sqrt 2 / 4 < (3 / 8 : ℝ) := by
  have h := div_lt_div_of_pos_right sqrt_two_lt_three_halves
    (by norm_num : (0 : ℝ) < 4)
  norm_num at h
  exact h

theorem counterexample_proved :
    ∀ U V : Matrix.unitaryGroup (Fin 3) ℂ,
      ¬ (symmetricModulus (witnessA + witnessB) ≤
        (Real.sqrt 2 : ℂ) •
          (unitaryConjugate U (symmetricModulus witnessA) +
            unitaryConjugate V (symmetricModulus witnessB))) := by
  intro U V hdom
  obtain ⟨w, hw, _, _, hL, hA, hB⟩ := witness_quadratic_bounds_proved U V
  have hq := quadraticForm_mono hdom w
  rw [quadraticForm_smul _ _ _ (by simp), quadraticForm_add] at hq
  simp only [Complex.ofReal_re] at hq
  have hup := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg 2)
  have hbound : (3 / 8 : ℝ) * squaredLength w ≤
      (Real.sqrt 2 / 4) * squaredLength w := by
    calc
      (3 / 8 : ℝ) * squaredLength w ≤
          Real.sqrt 2 * ((1 / 8 : ℝ) * squaredLength w +
            (1 / 8 : ℝ) * squaredLength w) := le_trans hL (le_trans hq hup)
      _ = (Real.sqrt 2 / 4) * squaredLength w := by ring
  exact (not_le_of_gt (mul_lt_mul_of_pos_right scalar_coefficient_gap hw)) hbound

theorem not_dominationConjecture_proved : ¬ DominationConjecture := by
  intro h
  obtain ⟨U, V, hUV⟩ := h 3 (by norm_num) witnessA witnessB
  exact counterexample_proved U V hUV

#assert_trust kernel modulus_eq_sqrt_proved
#assert_trust kernel modulus_of_positive_square
#assert_trust kernel rankOne_posSemidef
#assert_trust kernel diagonal_table_posSemidef
#assert_trust kernel rightModulusA_posSemidef
#assert_trust kernel axialModulus_posSemidef
#assert_trust kernel leftModulusB_posSemidef
#assert_trust kernel rightModulusSum_posSemidef
#assert_trust kernel leftModulusSum_posSemidef
#assert_trust kernel missingA_posSemidef
#assert_trust kernel missingB_posSemidef
#assert_trust kernel modulus_witnessA
#assert_trust kernel modulus_witnessA_adjoint
#assert_trust kernel modulus_witnessB
#assert_trust kernel modulus_witnessB_adjoint
#assert_trust kernel modulus_sum
#assert_trust kernel modulus_sum_adjoint
#assert_trust kernel symmetricModulus_A
#assert_trust kernel symmetricModulus_B
#assert_trust kernel symmetricModulus_sum
#assert_trust kernel symmetricA_decomposition
#assert_trust kernel symmetricB_decomposition
#assert_trust kernel witness_moduli_proved
#assert_trust kernel squaredLength_pos
#assert_trust kernel two_vector_orthogonal_proved
#assert_trust kernel quadraticForm_add
#assert_trust kernel quadraticForm_sub
#assert_trust kernel quadraticForm_smul
#assert_trust kernel quadraticForm_one
#assert_trust kernel quadraticForm_rankOne_zero
#assert_trust kernel quadraticForm_nonneg
#assert_trust kernel quadraticForm_mono
#assert_trust kernel unitaryConjugate_add
#assert_trust kernel unitaryConjugate_sub
#assert_trust kernel unitaryConjugate_smul
#assert_trust kernel unitaryConjugate_one
#assert_trust kernel unitaryConjugate_rankOne
#assert_trust kernel unitaryConjugate_posSemidef
#assert_trust kernel upper_bound_of_decomposition
#assert_trust kernel symmetricSum_lower_bound
#assert_trust kernel witness_quadratic_bounds_proved
#assert_trust kernel scalar_squared_gap
#assert_trust kernel sqrt_two_lt_three_halves
#assert_trust kernel scalar_coefficient_gap
#assert_trust kernel counterexample_proved
#assert_trust kernel not_dominationConjecture_proved

#print axioms modulus_eq_sqrt_proved
#print axioms modulus_of_positive_square
#print axioms rankOne_posSemidef
#print axioms diagonal_table_posSemidef
#print axioms rightModulusA_posSemidef
#print axioms axialModulus_posSemidef
#print axioms leftModulusB_posSemidef
#print axioms rightModulusSum_posSemidef
#print axioms leftModulusSum_posSemidef
#print axioms missingA_posSemidef
#print axioms missingB_posSemidef
#print axioms modulus_witnessA
#print axioms modulus_witnessA_adjoint
#print axioms modulus_witnessB
#print axioms modulus_witnessB_adjoint
#print axioms modulus_sum
#print axioms modulus_sum_adjoint
#print axioms symmetricModulus_A
#print axioms symmetricModulus_B
#print axioms symmetricModulus_sum
#print axioms symmetricA_decomposition
#print axioms symmetricB_decomposition
#print axioms witness_moduli_proved
#print axioms squaredLength_pos
#print axioms two_vector_orthogonal_proved
#print axioms quadraticForm_add
#print axioms quadraticForm_sub
#print axioms quadraticForm_smul
#print axioms quadraticForm_one
#print axioms quadraticForm_rankOne_zero
#print axioms quadraticForm_nonneg
#print axioms quadraticForm_mono
#print axioms unitaryConjugate_add
#print axioms unitaryConjugate_sub
#print axioms unitaryConjugate_smul
#print axioms unitaryConjugate_one
#print axioms unitaryConjugate_rankOne
#print axioms unitaryConjugate_posSemidef
#print axioms upper_bound_of_decomposition
#print axioms symmetricSum_lower_bound
#print axioms witness_quadratic_bounds_proved
#print axioms scalar_squared_gap
#print axioms sqrt_two_lt_three_halves
#print axioms scalar_coefficient_gap
#print axioms counterexample_proved
#print axioms not_dominationConjecture_proved

end NLA.MI06
