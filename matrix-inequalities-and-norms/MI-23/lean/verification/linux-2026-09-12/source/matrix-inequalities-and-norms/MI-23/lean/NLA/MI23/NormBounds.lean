/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Dimension-free entry and Frobenius bounds for the genuine Euclidean operator norm.
-/
import NLA.MI23.SpectralNorm

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI23

theorem entry_le_operatorNorm {n : ℕ} (A : Mat n) (i j : Fin n) :
    ‖A i j‖ ≤ operatorNorm A := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  let e : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Pi.single j 1)
  have he : ‖e‖ = 1 := by simp [e]
  have hcoord : (T e).ofLp i = A i j := by
    simp only [T, e, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_single_one]
    rfl
  calc
    ‖A i j‖ = ‖(T e).ofLp i‖ := by rw [hcoord]
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = operatorNorm A := by rw [he, mul_one]; rfl

theorem operatorNorm_posSemidef_le_trace {n : ℕ} (A : Mat n) (hA : A.PosSemidef) :
    operatorNorm A ≤ A.trace.re := by
  have ht : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum]
    congr 1
  rw [operatorNorm_eq_eigenvalueNorm A hA.isHermitian, ht]
  apply (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i)).mpr
  intro i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
    using hi

theorem trace_gram_eq_frobeniusSquared {n : ℕ} (A : Mat n) :
    (Aᴴ * A).trace.re = frobeniusSquared A := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, frobeniusSquared]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem operatorNorm_sq_le_frobeniusSquared {n : ℕ} (A : Mat n) :
    operatorNorm A ^ 2 ≤ frobeniusSquared A := by
  have h := operatorNorm_posSemidef_le_trace (Aᴴ * A)
    (Matrix.posSemidef_conjTranspose_mul_self A)
  rw [trace_gram_eq_frobeniusSquared] at h
  change ‖A‖ ^ 2 ≤ _
  change ‖Aᴴ * A‖ ≤ _ at h
  simpa only [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two] using h

theorem operator_norm_bounds_proved {n : ℕ} (A : Mat n) (i j : Fin n) :
    Complex.normSq (A i j) ≤ operatorNorm A ^ 2 ∧
      operatorNorm A ^ 2 ≤ frobeniusSquared A := by
  constructor
  · rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (entry_le_operatorNorm A i j) 2
  · exact operatorNorm_sq_le_frobeniusSquared A

end NLA.MI23
