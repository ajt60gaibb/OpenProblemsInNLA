import NLA.Proofs.RA10.SelectedProjectionRank

/-! RA-10: the frozen functional truncation is the supported functional
calculus on the actual selected projection, even when `f 0 > 0` and selected
eigenvalues vanish. The full transfer target remains open. -/
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

theorem selectedProjection_functionMatrix {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q)
    (f : ℝ → ℝ) :
    selectedProjection k Q * NLA.Statements.RA10.FunctionMatrix f eigenvalues Q *
      selectedProjection k Q =
        NLA.Statements.RA10.FunctionTruncation k f eigenvalues Q := by
  let d : Fin n → ℝ := fun a => if a.val < k then 1 else 0
  let w : Fin n → ℝ := fun a => f (eigenvalues a)
  let wd : Fin n → ℝ := fun a => if a.val < k then f (eigenvalues a) else 0
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d
  let F : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal w
  have hQTQ : Q.transpose * Q = 1 := by
    rcases h with ⟨_, _, hQ, _⟩
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b
  have hP : selectedProjection k Q = Q * D * Q.transpose := by
    calc
      selectedProjection k Q = NLA.Statements.RA10.SpectralMatrix d Q := by
        ext i j
        simp only [selectedProjection, Matrix.of_apply,
          NLA.Statements.RA10.SpectralMatrix]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a.val < k <;> simp [d, ha]
      _ = Q * D * Q.transpose := spectralMatrix_eq_diagonal d Q
  have hF : NLA.Statements.RA10.FunctionMatrix f eigenvalues Q =
      Q * F * Q.transpose := by
    exact spectralMatrix_eq_diagonal w Q
  have hT : NLA.Statements.RA10.FunctionTruncation k f eigenvalues Q =
      Q * Matrix.diagonal wd * Q.transpose := by
    calc
      NLA.Statements.RA10.FunctionTruncation k f eigenvalues Q =
          NLA.Statements.RA10.SpectralMatrix wd Q := by
        ext i j
        simp only [NLA.Statements.RA10.FunctionTruncation, Matrix.of_apply,
          NLA.Statements.RA10.SpectralMatrix]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a.val < k <;> simp [wd, ha]
      _ = Q * Matrix.diagonal wd * Q.transpose := spectralMatrix_eq_diagonal wd Q
  have hDFD : D * F * D = Matrix.diagonal wd := by
    simp only [D, F, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    by_cases ha : a.val < k <;> simp [d, w, wd, ha]
  rw [hP, hF, hT]
  calc
    (Q * D * Q.transpose) * (Q * F * Q.transpose) * (Q * D * Q.transpose)
        = (Q * D) * (Q.transpose * Q) * F * (Q.transpose * Q) * D * Q.transpose := by
            simp only [Matrix.mul_assoc]
    _ = Q * (D * F * D) * Q.transpose := by
      rw [hQTQ]
      simp [Matrix.mul_assoc]
    _ = Q * Matrix.diagonal wd * Q.transpose := by rw [hDFD]

#assert_trust kernel selectedProjection_functionMatrix
#print axioms selectedProjection_functionMatrix

end NLA.Proofs.RA10
