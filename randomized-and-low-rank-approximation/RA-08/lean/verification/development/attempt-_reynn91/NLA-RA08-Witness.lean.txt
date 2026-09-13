/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact algebra for Matthew J. Colbrook's unchanged RA-08 witness.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA.
-/
import NLA.RA08.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08

theorem witnessFunction_admissible : AdmissibleFunction witnessFunction := by
  refine ⟨?_, ⟨convex_Ici 0, ?_⟩, ?_, ?_⟩
  · exact (continuous_id.min continuous_const).continuousOn
  · intro x hx y hy a b ha hb hab
    change a * min x 1 + b * min y 1 ≤ min (a * x + b * y) 1
    apply le_min
    · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
    · calc
        a * min x 1 + b * min y 1 ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
        _ = 1 := by simpa using hab
  · intro x hx y hy hxy
    exact min_le_min hxy le_rfl
  · intro x hx
    exact le_min hx zero_le_one

theorem witnessT_pos : 0 < witnessT := by norm_num [witnessT]

theorem witnessB_add_T_lt_one : witnessB + witnessT < 1 := by
  norm_num [witnessB, witnessT]

theorem witnessU_orthogonal : witnessU.transpose * witnessU = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessU, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]

theorem witnessF_symmetric : witnessF.transpose = witnessF := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [witnessF, Matrix.transpose_apply]

theorem witnessF_idempotent : witnessF ^ 2 = witnessF := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, witnessF, Matrix.mul_apply, Fin.sum_univ_succ]

theorem real_gram_psd {n : ℕ} (A : RealMatrix n) :
    (A.transpose * A).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self A

theorem witnessF_psd : witnessF.PosSemidef := by
  have h := real_gram_psd witnessF
  rw [witnessF_symmetric, ← pow_two, witnessF_idempotent] at h
  exact h

theorem witnessF_complement_psd : (1 - witnessF).PosSemidef := by
  have h := real_gram_psd (1 - witnessF)
  have ht : (1 - witnessF).transpose = 1 - witnessF := by
    simp only [transpose_sub, transpose_one, witnessF_symmetric]
  have hi : (1 - witnessF) * (1 - witnessF) = 1 - witnessF := by
    have hmul : witnessF * witnessF = witnessF := by
      simpa only [pow_two] using witnessF_idempotent
    simp only [mul_sub, sub_mul, one_mul, mul_one, hmul,
      sub_self, sub_zero]
  rwa [ht, hi] at h

theorem witnessApproximation_psd : witnessApproximation.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [witnessA, witnessB]

theorem witnessMatrix_psd : witnessMatrix.PosSemidef :=
  witnessApproximation_psd.add (witnessF_psd.smul witnessT_pos.le)

theorem witness_order : witnessApproximation ≤ witnessMatrix := by
  change (witnessMatrix - witnessApproximation).PosSemidef
  simpa only [witnessMatrix, add_sub_cancel_left] using witnessF_psd.smul witnessT_pos.le

theorem real_length_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simpa only [star_trivial] using dotProduct_star_self_nonneg x

theorem real_gram_quadratic {n : ℕ} (A : RealMatrix n) (x : Fin n → ℝ) :
    x ⬝ᵥ ((A.transpose * A) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem witnessF_quadratic (x : Fin 6 → ℝ) :
    x ⬝ᵥ (witnessF *ᵥ x) = (witnessF *ᵥ x) ⬝ᵥ (witnessF *ᵥ x) := by
  have h := real_gram_quadratic witnessF x
  rwa [witnessF_symmetric, ← pow_two, witnessF_idempotent] at h

theorem witnessApproximation_quadratic (x : Fin 6 → ℝ) :
    x ⬝ᵥ (witnessApproximation *ᵥ x) =
      (1 / 2 : ℝ) * (x 0) ^ 2 + witnessB * (x 1) ^ 2 + witnessA * (x 2) ^ 2 := by
  simp [witnessApproximation, dotProduct, mulVec, diagonal, Fin.sum_univ_succ]
  ring

theorem witnessMatrix_quadratic (x : Fin 6 → ℝ) :
    x ⬝ᵥ (witnessMatrix *ᵥ x) =
      (1 / 2 : ℝ) * (x 0) ^ 2 + witnessB * (x 1) ^ 2 + witnessA * (x 2) ^ 2 +
        witnessT * ((witnessF *ᵥ x) ⬝ᵥ (witnessF *ᵥ x)) := by
  simp only [witnessMatrix, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
    witnessApproximation_quadratic, witnessF_quadratic, smul_eq_mul]

theorem witnessMatrix_posDef : witnessMatrix.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos witnessMatrix_psd.isHermitian
  intro x hx
  change 0 < x ⬝ᵥ (witnessMatrix *ᵥ x)
  by_contra h
  have hq := le_of_not_gt h
  rw [witnessMatrix_quadratic] at hq
  norm_num [witnessA, witnessB, witnessT] at hq
  have hF := real_length_nonneg (witnessF *ᵥ x)
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
  have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 2)]
  have hz : (witnessF *ᵥ x) ⬝ᵥ (witnessF *ᵥ x) = 0 := by
    nlinarith
  have hv : witnessF *ᵥ x = 0 := dotProduct_self_eq_zero.mp hz
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  have h5 := congrFun hv 5
  norm_num [witnessF, mulVec, dotProduct, Fin.sum_univ_succ, h0, h1, h2] at h3 h4 h5
  apply hx
  ext i
  fin_cases i <;> simp_all

theorem witness_data_proved :
    AdmissibleFunction witnessFunction ∧ witnessFunction 0 = 0 ∧
    0 < witnessT ∧ witnessB + witnessT < 1 ∧
    witnessU.transpose * witnessU = 1 ∧
    witnessF ^ 2 = witnessF ∧ witnessF.PosSemidef ∧
    (1 - witnessF).PosSemidef ∧ witnessApproximation.PosSemidef ∧
    witnessMatrix.PosDef ∧ witnessApproximation ≤ witnessMatrix := by
  exact ⟨witnessFunction_admissible, by norm_num [witnessFunction], witnessT_pos,
    witnessB_add_T_lt_one, witnessU_orthogonal, witnessF_idempotent, witnessF_psd,
    witnessF_complement_psd, witnessApproximation_psd, witnessMatrix_posDef, witness_order⟩

#assert_trust kernel witnessFunction_admissible
#assert_trust kernel witnessF_idempotent
#assert_trust kernel witnessMatrix_psd
#assert_trust kernel witness_data_proved
#print axioms witnessFunction_admissible
#print axioms witnessF_idempotent
#print axioms witnessMatrix_psd
#print axioms witness_data_proved

end NLA.RA08
