import NLA.Proofs.RA10.RidgeScalar
import NLA.Proofs.RA10.SelectedCompressionComparison
import NLA.Proofs.RA10.SelectedCompressionTail

/-! RA-10 source Equation (12): exact coefficient-one ridge trace loss of the
actual selected compression in the positive-cutoff branch. This is a partial
gate; the source Eq. (13) and frozen Target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem ridgeLoss_trace_spectralMatrix {n : ℕ}
    (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ a b, ∑ i, Q i a * Q i b = if a = b then 1 else 0) :
    Matrix.trace (NLA.Statements.RA10.SpectralMatrix d Q) = ∑ a : Fin n, d a := by
  simp only [Matrix.trace, Matrix.diag,
    NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  calc
    (∑ i : Fin n, ∑ a : Fin n, d a * Q i a * Q i a) =
        ∑ a : Fin n, ∑ i : Fin n, d a * Q i a * Q i a :=
      Finset.sum_comm
    _ = ∑ a : Fin n, d a * (∑ i : Fin n, Q i a * Q i a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ a : Fin n, d a := by
      apply Finset.sum_congr rfl
      intro a _
      have haa : (∑ i : Fin n, Q i a * Q i a) = 1 := by
        simpa using hQ a a
      rw [haa, mul_one]

private theorem ridgeLoss_atom_mono {s a b : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hba : b ≤ a) :
    ridgeAtom s b ≤ ridgeAtom s a := by
  have hsb : 0 < s + b := by linarith
  have hsa : 0 < s + a := by linarith
  unfold ridgeAtom
  apply (div_le_div_iff₀ hsb hsa).2
  nlinarith [mul_nonneg (le_of_lt hs) (sub_nonneg.mpr hba)]

theorem matchedLeading_ridge_loss_nonneg_le {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    {s : ℝ} (hs : 0 < s)
    (hc : 0 < eigenvaluesA ⟨k - 1, by omega⟩) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let C := selectedProjection k QAhat * A * selectedProjection k QAhat
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    let L_s := (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) -
      Matrix.trace (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC)
    0 ≤ L_s ∧ L_s ≤ L / (s + c) := by
  let c := eigenvaluesA ⟨k - 1, by omega⟩
  let C := selectedProjection k QAhat * A * selectedProjection k QAhat
  let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
  let L_s := (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) -
    Matrix.trace (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC)
  change 0 ≤ L_s ∧ L_s ≤ L / (s + c)
  have htraceC : Matrix.trace C =
      ∑ i : Fin n, if i.val < k then eigenvaluesC i else 0 :=
    selectedCompression_trace_prefix (Nat.le_of_lt hkn) hAhat hC
  have htraceF :
      Matrix.trace (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) =
        ∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesC i) else 0 := by
    change Matrix.trace (NLA.Statements.RA10.SpectralMatrix
      (fun i => ridgeAtom s (eigenvaluesC i)) QC) = _
    rw [ridgeLoss_trace_spectralMatrix _ QC hC.2.2.1]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k
    · simp [hi]
    · have hitail : eigenvaluesC i = 0 :=
        selectedCompression_eigenvalues_tail_zero (Nat.le_of_lt hkn) hAhat hC i
          (Nat.le_of_not_gt hi)
      simp [hi, hitail, ridgeAtom]
  have hLossF : L_s =
      ∑ i : Fin n,
        if i.val < k then ridgeAtom s (eigenvaluesA i) - ridgeAtom s (eigenvaluesC i)
        else 0 := by
    dsimp [L_s]
    rw [htraceF, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k <;> simp [hi]
  have hLoss : L =
      ∑ i : Fin n, if i.val < k then eigenvaluesA i - eigenvaluesC i else 0 := by
    dsimp [L]
    rw [htraceC, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k <;> simp [hi]
  have hpoint (i : Fin n) (hi : i.val < k) :
      0 ≤ ridgeAtom s (eigenvaluesA i) - ridgeAtom s (eigenvaluesC i) ∧
      ridgeAtom s (eigenvaluesA i) - ridgeAtom s (eigenvaluesC i) ≤
        (eigenvaluesA i - eigenvaluesC i) / (s + c) := by
    have hindex : i ≤ (⟨k - 1, by omega⟩ : Fin n) :=
      Fin.le_iff_val_le_val.mpr (by change i.val ≤ k - 1; omega)
    have hca : c ≤ eigenvaluesA i := hA.2.1 hindex
    have hcmp := selectedCompression_eigenvalues_nonneg_le
      (Nat.le_of_lt hkn) hA hAhat hC i hi
    have hmono := ridgeLoss_atom_mono hs hcmp.1 hcmp.2
    have hdiff : 0 ≤ ridgeAtom s (eigenvaluesA i) - ridgeAtom s (eigenvaluesC i) :=
      sub_nonneg.mpr hmono
    constructor
    · exact hdiff
    · have habs := ridgeAtom_abs_sub_le hs hc hca hcmp.1
      rwa [abs_of_nonneg hdiff, abs_of_nonneg (sub_nonneg.mpr hcmp.2)] at habs
  constructor
  · rw [hLossF]
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i.val < k
    · simpa [hi] using (hpoint i hi).1
    · simp [hi]
  · rw [hLossF, hLoss]
    calc
      (∑ i : Fin n,
          if i.val < k then ridgeAtom s (eigenvaluesA i) - ridgeAtom s (eigenvaluesC i)
          else 0) ≤
          ∑ i : Fin n,
            if i.val < k then (eigenvaluesA i - eigenvaluesC i) / (s + c)
            else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i.val < k
        · simpa [hi] using (hpoint i hi).2
        · simp [hi]
      _ = (∑ i : Fin n,
            if i.val < k then eigenvaluesA i - eigenvaluesC i else 0) / (s + c) := by
        calc
          (∑ i : Fin n,
              if i.val < k then (eigenvaluesA i - eigenvaluesC i) / (s + c)
              else 0) =
              ∑ i : Fin n,
                (if i.val < k then eigenvaluesA i - eigenvaluesC i else 0) / (s + c) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i.val < k <;> simp [hi]
          _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul]

#assert_trust kernel matchedLeading_ridge_loss_nonneg_le
#print axioms matchedLeading_ridge_loss_nonneg_le

end NLA.Proofs.RA10
