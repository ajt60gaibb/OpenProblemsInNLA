import NLA.Proofs.RA10.RidgeResolventMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Module

/-! RA-10 exact noncommutative ridge resolvent product gate. This proves
shifted invertibility and both matrix multiplication orders used by the source.
The positive-part ridge compression and nuclear-norm estimates remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem spectralShift_isUnit {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) := by
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
  have hQunit : IsUnit Q := isUnit_iff_exists.mpr ⟨Q.transpose, hQQT, hQTQ⟩
  have hQTunit : IsUnit Q.transpose := isUnit_iff_exists.mpr ⟨Q, hQTQ, hQQT⟩
  have hDunit : IsUnit (Matrix.diagonal ds) := by
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro a
    apply isUnit_iff_ne_zero.mpr
    exact ne_of_gt (show 0 < ds a by dsimp [ds]; linarith [hvalues a])
  rw [hshift]
  exact (hQunit.mul hDunit).mul hQTunit

theorem ridgeFunctionMatrix_sub_product_left {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesC : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ * (C - A) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) := by
  have hunit : IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) ↔
      IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C) := by
    constructor <;> intro _
    · exact spectralShift_isUnit hs hC
    · exact spectralShift_isUnit hs hA
  have hdiff :
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C) -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) = C - A := by
    module
  rw [ridgeFunctionMatrix_sub hs hA hC, Matrix.inv_sub_inv hunit, hdiff]

theorem ridgeFunctionMatrix_sub_product_right {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesC : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ * (C - A) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
  have hunit : IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C) ↔
      IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) := by
    constructor <;> intro _
    · exact spectralShift_isUnit hs hA
    · exact spectralShift_isUnit hs hC
  have hdiff :
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C) = -(C - A) := by
    module
  have hproduct :
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ =
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ * (C - A) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
    calc
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ -
          (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ =
          -((s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ -
            (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by module
      _ = -((s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ *
            ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) -
              (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)) *
            (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
        rw [Matrix.inv_sub_inv hunit]
      _ = (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ * (C - A) *
            (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
        rw [hdiff]
        simp only [mul_neg, neg_mul, neg_neg]
  rw [ridgeFunctionMatrix_sub hs hA hC, hproduct]

#assert_trust kernel spectralShift_isUnit
#assert_trust kernel ridgeFunctionMatrix_sub_product_left
#assert_trust kernel ridgeFunctionMatrix_sub_product_right
#print axioms ridgeFunctionMatrix_sub_product_left
#print axioms ridgeFunctionMatrix_sub_product_right

end NLA.Proofs.RA10
