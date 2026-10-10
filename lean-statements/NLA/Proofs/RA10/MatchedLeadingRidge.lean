import NLA.Proofs.RA10.RidgeResolventProduct

/-! RA-10 matched leading-spectrum matrix in the supplied selected basis.
This gives the exact matrix equality underlying source Equation (14); its
nuclear-norm ideal-property estimate and the full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem matchedLeading_orderedPSD {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)
      (fun a : Fin n => if a.val < k then eigenvaluesA a else 0) QAhat := by
  rcases hA with ⟨hvalues, horder, _, _⟩
  rcases hAhat with ⟨_, _, hQhat, _⟩
  refine ⟨?_, ?_, hQhat, ?_⟩
  · intro a
    by_cases ha : a.val < k <;> simp [ha, hvalues a]
  · intro a b hab
    by_cases ha : a.val < k
    · by_cases hb : b.val < k
      · simpa [ha, hb] using horder hab
      · simp [ha, hb, hvalues a]
    · have hb : ¬ b.val < k := by
        exact not_lt_of_ge (le_trans (not_lt.mp ha) (Fin.le_iff_val_le_val.mp hab))
      simp [ha, hb]
  · ext i j
    simp only [NLA.Statements.RA10.FunctionTruncation,
      NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < k <;> simp [ha]

theorem matchedLeading_ridgeFunctionMatrix {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (eigenvaluesA : Fin n → ℝ)
    (QAhat : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s)
      (fun a : Fin n => if a.val < k then eigenvaluesA a else 0) QAhat =
    NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat := by
  ext i j
  simp only [NLA.Statements.RA10.FunctionMatrix,
    NLA.Statements.RA10.FunctionTruncation,
    NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val < k <;> simp [ha, ridgeAtom]

theorem matchedLeading_ridgeProduct_right {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) +
        NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat - C) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) := by
  have hB0 := matchedLeading_orderedPSD (k := k) hA hAhat
  have hproduct := ridgeFunctionMatrix_sub_product_right hs hC hB0
  rw [matchedLeading_ridgeFunctionMatrix hs eigenvaluesA QAhat] at hproduct
  exact hproduct

#assert_trust kernel matchedLeading_orderedPSD
#assert_trust kernel matchedLeading_ridgeFunctionMatrix
#assert_trust kernel matchedLeading_ridgeProduct_right
#print axioms matchedLeading_ridgeProduct_right

end NLA.Proofs.RA10
