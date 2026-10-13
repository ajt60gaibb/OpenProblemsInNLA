import NLA.Proofs.RA10.OrderedSpectralNuclearPerturbation

/-! Exact nuclear norms in any supplied orthonormal basis, including the
selected zero eigenspaces. This does not choose or alter a spectral basis. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem nuclearNorm_spectralMatrix {n : ℕ}
    (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ a b, ∑ i, Q i a * Q i b = if a = b then 1 else 0) :
    NLA.Statements.RA10.NuclearNorm (NLA.Statements.RA10.SpectralMatrix d Q) =
      ∑ i : Fin n, |d i| := by
  have hQtQ : Q.transpose * Q = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b
  rw [spectralMatrix_factor,
    nuclearNorm_orthogonal_conj Q (Matrix.diagonal d) hQtQ (mul_eq_one_comm.mp hQtQ)]
  exact nuclearNorm_diagonal d

/-- Both truncations retain exactly the specified first k basis vectors. -/
theorem nuclearNorm_functionTruncation_sub {n k : ℕ}
    (f g : ℝ → ℝ) (a b : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, ∑ l, Q l i * Q l j = if i = j then 1 else 0) :
    NLA.Statements.RA10.NuclearNorm
        (NLA.Statements.RA10.FunctionTruncation k f a Q -
          NLA.Statements.RA10.FunctionTruncation k g b Q) =
      ∑ i : Fin n, if i.val < k then |f (a i) - g (b i)| else 0 := by
  have hmatrix :
      NLA.Statements.RA10.FunctionTruncation k f a Q -
          NLA.Statements.RA10.FunctionTruncation k g b Q =
        NLA.Statements.RA10.SpectralMatrix
          (fun i : Fin n => if i.val < k then f (a i) - g (b i) else 0) Q := by
    ext i j
    simp only [NLA.Statements.RA10.FunctionTruncation,
      NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _hl
    by_cases hl : l.val < k
    · simp only [if_pos hl]
      ring
    · simp [hl]
  rw [hmatrix, nuclearNorm_spectralMatrix _ Q hQ]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : i.val < k <;> simp [hi]

/-- The best selected spectral tail, for any function nonnegative on the spectrum. -/
theorem nuclearNorm_functionMatrix_sub_truncation {n k : ℕ}
    (f : ℝ → ℝ) (a : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, ∑ l, Q l i * Q l j = if i = j then 1 else 0)
    (hf : ∀ i, 0 ≤ f (a i)) :
    NLA.Statements.RA10.NuclearNorm
        (NLA.Statements.RA10.FunctionMatrix f a Q -
          NLA.Statements.RA10.FunctionTruncation k f a Q) =
      ∑ i : Fin n, if k ≤ i.val then f (a i) else 0 := by
  have hmatrix :
      NLA.Statements.RA10.FunctionMatrix f a Q -
          NLA.Statements.RA10.FunctionTruncation k f a Q =
        NLA.Statements.RA10.SpectralMatrix
          (fun i : Fin n => if k ≤ i.val then f (a i) else 0) Q := by
    ext i j
    simp only [NLA.Statements.RA10.FunctionMatrix,
      NLA.Statements.RA10.FunctionTruncation,
      NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _hl
    by_cases hl : l.val < k
    · simp [hl, Nat.not_le_of_gt hl]
    · simp [hl, Nat.le_of_not_gt hl]
  rw [hmatrix, nuclearNorm_spectralMatrix _ Q hQ]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : k ≤ i.val <;> simp [hi, abs_of_nonneg (hf i)]

theorem nuclearNorm_orderedPSD_tail {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A a Q) :
    NLA.Statements.RA10.NuclearNorm
        (A - NLA.Statements.RA10.FunctionTruncation k (fun t => t) a Q) =
      ∑ i : Fin n, if k ≤ i.val then a i else 0 := by
  rw [hA.2.2.2]
  exact nuclearNorm_functionMatrix_sub_truncation (fun t => t) a Q hA.2.2.1 hA.1

theorem orderedPSD_cutoff_pos_of_tail_pos {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A a Q)
    (hτ : 0 < ∑ i : Fin n, if k ≤ i.val then a i else 0) :
    0 < a ⟨k - 1, by omega⟩ := by
  by_contra hc
  have hcle : a ⟨k - 1, by omega⟩ ≤ 0 := le_of_not_gt hc
  have hzero : (∑ i : Fin n, if k ≤ i.val then a i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hi : k ≤ i.val
    · rw [if_pos hi]
      apply le_antisymm _ (hA.1 i)
      exact (hA.2.1 (show (⟨k - 1, by omega⟩ : Fin n) ≤ i from
        Fin.le_iff_val_le_val.mpr (by change k - 1 ≤ i.val; omega))).trans hcle
    · simp [hi]
  linarith

#assert_trust kernel nuclearNorm_spectralMatrix
#assert_trust kernel nuclearNorm_functionTruncation_sub
#assert_trust kernel nuclearNorm_functionMatrix_sub_truncation
#assert_trust kernel nuclearNorm_orderedPSD_tail
#assert_trust kernel orderedPSD_cutoff_pos_of_tail_pos
#print axioms nuclearNorm_functionTruncation_sub

end NLA.Proofs.RA10
