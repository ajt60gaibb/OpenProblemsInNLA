import NLA.Proofs.RA10.SelectedCompressionTail
import NLA.Proofs.RA10.SelectedCompressionComparison

/-! RA-10 source Equation (11), scalar stage: the exact coefficient-one
positive-part deficit sum is bounded by the trace loss. The matrix positive
part identification and frozen Target remain separate obligations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem matchedLeading_defect_sum_le_loss {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    (∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0) ≤ L := by
  let c := eigenvaluesA ⟨k - 1, by omega⟩
  let P := selectedProjection k QAhat
  let C := P * A * P
  change (∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0) ≤
    (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
  have htrace : Matrix.trace C =
      ∑ i : Fin n, if i.val < k then eigenvaluesC i else 0 :=
    selectedCompression_trace_prefix (Nat.le_of_lt hkn) hAhat hC
  have hpoint (i : Fin n) (hi : i.val < k) :
      max (c - eigenvaluesC i) 0 ≤ eigenvaluesA i - eigenvaluesC i := by
    have hindex : i.val ≤ k - 1 := by omega
    have hic : i ≤ (⟨k - 1, by omega⟩ : Fin n) :=
      Fin.le_iff_val_le_val.mpr (by simpa using hindex)
    have hca : c ≤ eigenvaluesA i := hA.2.1 hic
    have hcmp := selectedCompression_eigenvalues_nonneg_le
      (Nat.le_of_lt hkn) hA hAhat hC i hi
    by_cases hzero : 0 ≤ c - eigenvaluesC i
    · rw [max_eq_left hzero]
      linarith
    · rw [max_eq_right (le_of_not_ge hzero)]
      linarith [hcmp.2]
  calc
    (∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0) ≤
        ∑ i : Fin n, if i.val < k then eigenvaluesA i - eigenvaluesC i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i.val < k
      · simpa [hi] using hpoint i hi
      · simp [hi]
    _ = (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) -
        (∑ i : Fin n, if i.val < k then eigenvaluesC i else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k <;> simp [hi]
    _ = (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) -
        Matrix.trace C := by rw [htrace]

#assert_trust kernel matchedLeading_defect_sum_le_loss
#print axioms matchedLeading_defect_sum_le_loss

end NLA.Proofs.RA10
