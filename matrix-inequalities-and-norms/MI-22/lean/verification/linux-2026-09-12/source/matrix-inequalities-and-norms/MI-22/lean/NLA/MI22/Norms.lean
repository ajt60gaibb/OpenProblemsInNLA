/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Genuine Euclidean norm bridges, adapted from the campaign's MI-23 spectral and
Frobenius proofs with attribution. Every result below is re-proved on MI-22's
frozen definitions. Department of Computing and Mathematical Sciences,
California Institute of Technology. AI-assisted formalization.
-/
import NLA.MI22.FunctionalCalculus

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI22

/-- Explicitly identify the selected L2 matrix norm with the project's continuous
Euclidean-map norm, avoiding reliance on an unrelated default matrix norm. -/
theorem operatorNorm_eq_l2 {n : ℕ} (A : Mat n) : operatorNorm A = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

theorem operatorNorm_nonneg {n : ℕ} (A : Mat n) : 0 ≤ operatorNorm A := norm_nonneg _

theorem operatorNorm_mul {n : ℕ} (A B : Mat n) :
    operatorNorm (A * B) ≤ operatorNorm A * operatorNorm B := by
  simpa only [operatorNorm_eq_l2] using Matrix.l2_opNorm_mul A B

theorem operatorNorm_eq_eigenvalueNorm {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    operatorNorm A = ‖(fun i => (hA.eigenvalues i : ℂ))‖ := by
  rw [operatorNorm_eq_l2]
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  rfl

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

theorem operatorNorm_gram {n : ℕ} (A : Mat n) :
    operatorNorm (Aᴴ * A) = operatorNorm A ^ 2 := by
  simp only [operatorNorm_eq_l2, Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]

theorem euclidean_norm_bounds_proved {n : ℕ} (A : Mat n) :
    operatorNorm A ^ 2 ≤ frobeniusSquared A ∧
    (∀ x : EuclideanSpace ℂ (Fin n), ∀ i : Fin n,
      ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i‖ ≤
        operatorNorm A * ‖x‖) := by
  constructor
  · have h := operatorNorm_posSemidef_le_trace (Aᴴ * A)
      (Matrix.posSemidef_conjTranspose_mul_self A)
    simpa only [trace_gram_eq_frobeniusSquared, operatorNorm_gram] using h
  · intro x i
    exact (PiLp.norm_apply_le _ i).trans
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).le_opNorm x)

theorem operatorNorm_eighth_power {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    operatorNorm (A ^ (8 : ℕ)) = operatorNorm A ^ (8 : ℕ) := by
  have h := hA.isSelfAdjoint.norm_pow_two_pow 3
  norm_num only [show (2 : ℕ) ^ 3 = 8 from rfl] at h
  simpa only [operatorNorm_eq_l2] using h

end NLA.MI22
