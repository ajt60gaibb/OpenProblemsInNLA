/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Universal complex-vector identities for the IE-23 matrices, including every
complex competing right inverse. These are exact actions and genuine squared
Euclidean norms, following Colbrook's proof and the Dokmanić–Gribonval matrix.
AI-assisted formalization, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE23.Matrices
import NLA.IE23.FourthPower

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

lemma witnessB_action (y : Vec 2) :
    witnessB.mulVec y = ![(y 0 + y 1) / 3, (2 * y 0 - y 1) / 3,
      (-y 0 + 2 * y 1) / 3] := by
  ext i
  fin_cases i <;>
    norm_num [witnessB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

lemma witnessX_action (y : Vec 2) : witnessX.mulVec y = ![0, y 0, y 1] := by
  ext i
  fin_cases i <;> simp [witnessX, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma witnessB_norm_identity (y : Vec 2) :
    euclideanNorm (witnessB.mulVec y) ^ 2 + Complex.normSq (y 0 + y 1) / 3 =
      euclideanNorm y ^ 2 := by
  simp only [euclideanNorm_sq_normSq, witnessB_action]
  norm_num [Fin.sum_univ_succ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  ring

lemma witnessX_norm_identity (y : Vec 2) :
    euclideanNorm (witnessX.mulVec y) = euclideanNorm y := by
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)).mp
  simp [euclideanNorm_sq_normSq, witnessX_action, Fin.sum_univ_succ]

lemma competitor_norming_action (Y : Mat 3 2) (hY : IsRightInverse witnessA Y) :
    Y.mulVec normingVector =
      ![(Y.mulVec normingVector) 0, 1 - (Y.mulVec normingVector) 0,
        -1 - (Y.mulVec normingVector) 0] := by
  have h := congrArg (fun M : Mat 2 2 => M.mulVec normingVector) hY
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  norm_num [witnessA, normingVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  ext i
  fin_cases i
  · rfl
  · simpa [Matrix.mulVec, dotProduct, normingVector, Fin.sum_univ_succ] using
      eq_sub_of_add_eq' h0
  · simpa [Matrix.mulVec, dotProduct, normingVector, Fin.sum_univ_succ] using
      eq_sub_of_add_eq' h1

lemma competitor_norm_identity (Y : Mat 3 2) (hY : IsRightInverse witnessA Y) :
    euclideanNorm (Y.mulVec normingVector) ^ 2 =
      2 + 3 * Complex.normSq ((Y.mulVec normingVector) 0) := by
  rw [euclideanNorm_sq_normSq]
  conv_lhs => rw [competitor_norming_action Y hY]
  norm_num [Fin.sum_univ_succ, Complex.normSq_apply]
  ring

lemma normingVector_ne_zero : normingVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [normingVector] at h0

lemma normingVector_lpNorm : lpNorm 4 normingVector = witnessNorm := by
  have h : lpNorm 4 normingVector ^ 4 = 2 := by
    rw [lpNorm_fourth_power]
    norm_num [normingVector, Fin.sum_univ_succ]
  have hs : (lpNorm 4 normingVector ^ 2) ^ 2 = (witnessNorm ^ 2) ^ 2 := by
    nlinarith [witnessNorm_pow_four]
  have hs2 := (sq_eq_sq₀ (sq_nonneg (lpNorm 4 normingVector))
    (sq_nonneg witnessNorm)).mp hs
  exact (sq_eq_sq₀ (lpNorm_nonneg _ _) witnessNorm_pos.le).mp hs2

lemma witnessB_norming_norm : euclideanNorm (witnessB.mulVec normingVector) = Real.sqrt 2 := by
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [euclideanNorm_sq_normSq, witnessB_action, normingVector, Fin.sum_univ_succ]

lemma witnessX_norming_norm : euclideanNorm (witnessX.mulVec normingVector) = Real.sqrt 2 := by
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [euclideanNorm_sq_normSq, witnessX_action, normingVector, Fin.sum_univ_succ]

lemma sqrt_two_div_witnessNorm : Real.sqrt 2 / witnessNorm = witnessNorm := by
  apply (div_eq_iff witnessNorm_pos.ne').mpr
  nlinarith [witnessNorm_sq]

end NLA.IE23
