import NLA.Proofs.RA10.SelectedSpectralNuclear
import NLA.Proofs.RA10.MatchedLeadingRidge

/-! RA-10 source Equations (16)–(18): arbitrary selected approximants.
These estimates use the actual frozen nuclear norm and retain every supplied
ordered basis. The compression estimate and full Target remain separate. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem selectedApproximant_spectral_error_le {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A a QA)
    (hB : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat b QB) :
    (∑ i : Fin n, if i.val < k then |a i - b i| else 0) +
        (∑ i : Fin n, if k ≤ i.val then a i else 0) ≤
      NLA.Statements.RA10.NuclearNorm
        (A - NLA.Statements.RA10.FunctionTruncation k (fun t => t) b QB) := by
  have h := orderedPSDSpectral_nuclear_perturbation hA
    (matchedLeading_orderedPSD (k := k) hB hB)
  have hsplit : (∑ i : Fin n, |a i - (if i.val < k then b i else 0)|) =
      (∑ i : Fin n, if i.val < k then |a i - b i| else 0) +
        (∑ i : Fin n, if k ≤ i.val then a i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i.val < k
    · simp [hi, Nat.not_le_of_gt hi]
    · simp [hi, Nat.le_of_not_gt hi, abs_of_nonneg (hA.1 i)]
  rwa [hsplit] at h

/-- Source (16), expressed as a bound by the actual nuclear excess. -/
theorem selectedApproximant_spectral_error_le_excess {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A a QA)
    (hB : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat b QB) :
    (∑ i : Fin n, if i.val < k then |a i - b i| else 0) ≤
      NLA.Statements.RA10.NuclearNorm
          (A - NLA.Statements.RA10.FunctionTruncation k (fun t => t) b QB) -
        (∑ i : Fin n, if k ≤ i.val then a i else 0) := by
  exact (le_sub_iff_add_le).mpr (selectedApproximant_spectral_error_le hA hB)

/-- Source (17): replacing selected eigenvalues costs at most their total error. -/
theorem selectedApproximant_matched_excess_le {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QB : Matrix (Fin n) (Fin n) ℝ}
    (hB : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat b QB) :
    NLA.Statements.RA10.NuclearNorm
          (A - NLA.Statements.RA10.FunctionTruncation k (fun t => t) a QB) -
        (∑ i : Fin n, if k ≤ i.val then a i else 0) ≤
      NLA.Statements.RA10.NuclearNorm
          (A - NLA.Statements.RA10.FunctionTruncation k (fun t => t) b QB) -
        (∑ i : Fin n, if k ≤ i.val then a i else 0) +
        (∑ i : Fin n, if i.val < k then |a i - b i| else 0) := by
  let B := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) b QB
  let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) a QB
  have hsplit : A - B₀ = (A - B) + (B - B₀) := by abel
  have hnorm : NLA.Statements.RA10.NuclearNorm (B - B₀) =
      ∑ i : Fin n, if i.val < k then |a i - b i| else 0 := by
    simpa only [abs_sub_comm] using
      nuclearNorm_functionTruncation_sub (k := k) (fun t => t) (fun t => t) b a QB hB.2.2.1
  have h := nuclearNorm_add_le (A - B) (B - B₀)
  rw [← hsplit, hnorm] at h
  dsimp [B, B₀] at h
  linarith

/-- Source (18), with the exact cutoff and the prescribed selected eigenvectors. -/
theorem selectedApproximant_ridge_difference_le {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A a QA)
    (hB : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat b QB)
    {s : ℝ} (hs : 0 < s) (hc : 0 < a ⟨k - 1, by omega⟩) :
    NLA.Statements.RA10.NuclearNorm
        (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) a QB -
          NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) b QB) ≤
      (∑ i : Fin n, if i.val < k then |a i - b i| else 0) /
        (s + a ⟨k - 1, by omega⟩) := by
  rw [nuclearNorm_functionTruncation_sub _ _ _ _ _ hB.2.2.1]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hi : i.val < k
  · simp only [hi, ↓reduceIte]
    have hindex : i ≤ (⟨k - 1, by omega⟩ : Fin n) :=
      Fin.le_iff_val_le_val.mpr (by change i.val ≤ k - 1; omega)
    exact ridgeAtom_abs_sub_le hs hc (hA.2.1 hindex) (hB.1 i)
  · simp [hi]

#assert_trust kernel selectedApproximant_spectral_error_le
#assert_trust kernel selectedApproximant_spectral_error_le_excess
#assert_trust kernel selectedApproximant_matched_excess_le
#assert_trust kernel selectedApproximant_ridge_difference_le
#print axioms selectedApproximant_spectral_error_le
#print axioms selectedApproximant_ridge_difference_le

end NLA.Proofs.RA10
