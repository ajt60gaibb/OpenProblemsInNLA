import NLA.Proofs.RA10.MatchedLeadingSupport
import Mathlib.Tactic.Ring

/-! RA-10 compression eigenvalue comparison, first exact dependency: every
positive eigenvector of the actual `C = P * A * P` lies in the selected
projector's range. The min-max comparison and full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

private theorem compressionSpectralMatrix_eq_diagonal {n : ℕ}
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

private theorem orderedSpectral_column_eigenvector {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvalues Q)
    (a : Fin n) :
    C *ᵥ (fun i => Q i a) = eigenvalues a • (fun i => Q i a) := by
  have hQTQ : Q.transpose * Q = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hC.2.2.1 i j
  have hCdiag : C = Q * Matrix.diagonal eigenvalues * Q.transpose := by
    calc
      C = NLA.Statements.RA10.SpectralMatrix eigenvalues Q := hC.2.2.2
      _ = Q * Matrix.diagonal eigenvalues * Q.transpose :=
        compressionSpectralMatrix_eq_diagonal eigenvalues Q
  have hsingle : Pi.single a (eigenvalues a) =
      eigenvalues a • Pi.single a (1 : ℝ) := by
    ext b
    by_cases hab : b = a <;> simp [hab]
  change C *ᵥ Q.col a = eigenvalues a • Q.col a
  rw [hCdiag, ← Matrix.mulVec_single_one Q a]
  calc
    (Q * Matrix.diagonal eigenvalues * Q.transpose) *ᵥ
        (Q *ᵥ Pi.single a (1 : ℝ)) =
        Q *ᵥ (Matrix.diagonal eigenvalues *ᵥ
          (Q.transpose *ᵥ (Q *ᵥ Pi.single a (1 : ℝ)))) := by
      simp only [← Matrix.mulVec_mulVec]
    _ = Q *ᵥ (Matrix.diagonal eigenvalues *ᵥ
          ((Q.transpose * Q) *ᵥ Pi.single a (1 : ℝ))) := by
      exact congrArg (fun z => Q *ᵥ (Matrix.diagonal eigenvalues *ᵥ z))
        (Matrix.mulVec_mulVec (Pi.single a (1 : ℝ)) Q.transpose Q)
    _ = Q *ᵥ (Matrix.diagonal eigenvalues *ᵥ Pi.single a (1 : ℝ)) := by
      rw [hQTQ, Matrix.one_mulVec]
    _ = Q *ᵥ Pi.single a (eigenvalues a) := by
      rw [Matrix.diagonal_mulVec_single]
      simp
    _ = eigenvalues a • (Q *ᵥ Pi.single a (1 : ℝ)) := by
      rw [hsingle]
      simp [Matrix.mulVec_smul]

theorem selectedCompression_positiveEigenvector_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (a : Fin n) (ha : 0 < eigenvaluesC a) :
    let P := selectedProjection k QAhat
    let v : Fin n → ℝ := fun i => QC i a
    P *ᵥ v = v := by
  dsimp
  let P := selectedProjection k QAhat
  let C := P * A * P
  let v : Fin n → ℝ := fun i => QC i a
  change P *ᵥ v = v
  have hPP : P * P = P := selectedProjection_idempotent (k := k) hAhat
  have hPC : P * C = C := by
    dsimp [C]
    calc
      P * (P * A * P) = (P * P) * A * P := by simp only [Matrix.mul_assoc]
      _ = P * A * P := by rw [hPP]
  have hCv : C *ᵥ v = eigenvaluesC a • v :=
    orderedSpectral_column_eigenvector hC a
  have hPv : eigenvaluesC a • (P *ᵥ v) = eigenvaluesC a • v := by
    calc
      eigenvaluesC a • (P *ᵥ v) = P *ᵥ (eigenvaluesC a • v) := by
        rw [Matrix.mulVec_smul]
      _ = P *ᵥ (C *ᵥ v) := by rw [hCv]
      _ = (P * C) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = C *ᵥ v := by rw [hPC]
      _ = eigenvaluesC a • v := hCv
  ext i
  have hi := congrFun hPv i
  exact (mul_left_cancel₀ (ne_of_gt ha)) (by simpa [smul_eq_mul] using hi)

#assert_trust kernel selectedCompression_positiveEigenvector_supported
#print axioms selectedCompression_positiveEigenvector_supported

end NLA.Proofs.RA10
