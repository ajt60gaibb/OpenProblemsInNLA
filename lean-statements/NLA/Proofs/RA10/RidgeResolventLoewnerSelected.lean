import NLA.Proofs.RA10.RidgeResolventLoewner

/-! RA-10 sharp selected-range resolvent bounds with the prescribed `QAhat`
and source cutoff `c = a_k`. These are Loewner bounds; nuclear ideal and
operator-norm consequences remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem spectralMatrix_psd {n : ℕ}
    (w : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    NLA.Statements.RA10.PositiveSemidefinite
      (NLA.Statements.RA10.SpectralMatrix w Q) := by
  constructor
  · intro i j
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · intro x
    rw [spectralMatrix_quadratic_form]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hw a) (sq_nonneg _)

private theorem selected_resolvent_eq_spectral {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    selectedProjection k QAhat *
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
        NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
      selectedProjection k QAhat =
    NLA.Statements.RA10.SpectralMatrix
      (fun a : Fin n => if a.val < k then 1 / (s + eigenvaluesA a) else 0) QAhat := by
  have hB0 := matchedLeading_orderedPSD (k := k) hA hAhat
  rw [← spectralShift_inverse hs hB0]
  rw [selectedProjection_functionMatrix hB0 (fun x => 1 / (s + x))]
  ext i j
  simp only [NLA.Statements.RA10.FunctionTruncation,
    NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val < k <;> simp [ha]

theorem matchedLeading_selectedResolvent_nonnegative {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (j : Fin n) (hj : j.val + 1 = k) :
    NLA.Statements.RA10.PositiveSemidefinite
      (selectedProjection k QAhat *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
          NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        selectedProjection k QAhat) := by
  rw [selected_resolvent_eq_spectral hs hA hAhat]
  apply spectralMatrix_psd
  intro a
  by_cases ha : a.val < k
  · simp only [ha, ite_true]
    have hpos : 0 < s + eigenvaluesA a := by linarith [hA.1 a]
    exact le_of_lt (one_div_pos.mpr hpos)
  · simp [ha]

theorem matchedLeading_selectedResolvent_upperBound {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (j : Fin n) (hj : j.val + 1 = k) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((1 / (s + eigenvaluesA j)) • selectedProjection k QAhat -
        selectedProjection k QAhat *
          (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
            NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
          selectedProjection k QAhat) := by
  let g : ℝ := 1 / (s + eigenvaluesA j)
  have hP : selectedProjection k QAhat =
      NLA.Statements.RA10.SpectralMatrix
        (fun a : Fin n => if a.val < k then 1 else 0) QAhat := by
    ext i l
    simp only [selectedProjection, NLA.Statements.RA10.SpectralMatrix,
      Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < k <;> simp [ha]
  have hrep :
      g • selectedProjection k QAhat -
        selectedProjection k QAhat *
          (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
            NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
          selectedProjection k QAhat =
        NLA.Statements.RA10.SpectralMatrix
          (fun a : Fin n => if a.val < k then g - 1 / (s + eigenvaluesA a) else 0)
          QAhat := by
    rw [selected_resolvent_eq_spectral hs hA hAhat, hP]
    ext i l
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < k <;> simp [ha] <;> ring
  change NLA.Statements.RA10.PositiveSemidefinite
    (g • selectedProjection k QAhat -
      selectedProjection k QAhat *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
          NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        selectedProjection k QAhat)
  rw [hrep]
  apply spectralMatrix_psd
  intro a
  by_cases ha : a.val < k
  · simp only [ha, ite_true]
    have haj : a ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      omega
    have hle : eigenvaluesA j ≤ eigenvaluesA a := hA.2.1 haj
    have hsC : 0 < s + eigenvaluesA j := by linarith [hA.1 j]
    have hsA : 0 < s + eigenvaluesA a := by linarith [hA.1 a]
    have heq : g - 1 / (s + eigenvaluesA a) =
        (eigenvaluesA a - eigenvaluesA j) /
          ((s + eigenvaluesA j) * (s + eigenvaluesA a)) := by
      dsimp [g]
      field_simp [ne_of_gt hsC, ne_of_gt hsA]
      ring
    rw [heq]
    exact div_nonneg (sub_nonneg.mpr hle) (le_of_lt (mul_pos hsC hsA))
  · simp [ha]

#assert_trust kernel matchedLeading_selectedResolvent_nonnegative
#assert_trust kernel matchedLeading_selectedResolvent_upperBound
#print axioms matchedLeading_selectedResolvent_upperBound

end NLA.Proofs.RA10
