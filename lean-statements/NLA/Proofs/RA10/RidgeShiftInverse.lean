import NLA.Proofs.RA10.RidgeScalar
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-! RA-10 ridge resolvent gate, stage one: the frozen spectral reciprocal
matrix is the actual inverse of `sI + A` for every supplied PSD eigenbasis.
The matrix ridge compression and transfer target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem spectralMatrix_eq_diagonal {n : ℕ}
    (w : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix w Q =
      Q * Matrix.diagonal w * Q.transpose := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem spectralShift_inverse {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.FunctionMatrix (fun x => 1 / (s + x)) eigenvalues Q =
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
  rcases h with ⟨hvalues, _, hQ, hA⟩
  have hQTQ : Q.transpose * Q = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b
  have hQQT : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQTQ
  have hrow (i j : Fin n) :
      (∑ a : Fin n, Q i a * Q j a) = if i = j then 1 else 0 := by
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hQQT
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hij
  let ds : Fin n → ℝ := fun a => s + eigenvalues a
  let dr : Fin n → ℝ := fun a => 1 / (s + eigenvalues a)
  have hshift : s • (1 : Matrix (Fin n) (Fin n) ℝ) + A =
      Q * Matrix.diagonal ds * Q.transpose := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [hA]
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, ds]
    calc
      s * (if i = j then (1 : ℝ) else 0) +
          ∑ a : Fin n, eigenvalues a * Q i a * Q j a =
          s * (∑ a : Fin n, Q i a * Q j a) +
            ∑ a : Fin n, eigenvalues a * Q i a * Q j a := by rw [hrow]
      _ = ∑ a : Fin n, Q i a * (s + eigenvalues a) * Q j a := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
  have hdiag : Matrix.diagonal ds * Matrix.diagonal dr = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst b
      have hpos : 0 < s + eigenvalues a := by linarith [hvalues a]
      simp [ds, dr, ne_of_gt hpos]
    · simp [hab]
  let R : Matrix (Fin n) (Fin n) ℝ := Q * Matrix.diagonal dr * Q.transpose
  have hright : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) * R = 1 := by
    rw [hshift]
    dsimp [R]
    calc
      (Q * Matrix.diagonal ds * Q.transpose) *
          (Q * Matrix.diagonal dr * Q.transpose) =
          Q * Matrix.diagonal ds * (Q.transpose * Q) *
            Matrix.diagonal dr * Q.transpose := by simp only [Matrix.mul_assoc]
      _ = Q * (Matrix.diagonal ds * Matrix.diagonal dr) * Q.transpose := by
        rw [hQTQ]
        simp [Matrix.mul_assoc]
      _ = 1 := by rw [hdiag]; simpa using hQQT
  have hinv : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ = R :=
    Matrix.inv_eq_right_inv hright
  change NLA.Statements.RA10.SpectralMatrix dr Q = _
  rw [spectralMatrix_eq_diagonal]
  exact hinv.symm

#assert_trust kernel spectralShift_inverse
#print axioms spectralShift_inverse

end NLA.Proofs.RA10
