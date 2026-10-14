import NLA.Proofs.RA10.HermitianPositivePart
import NLA.Proofs.RA10.CustomPSDMathlibBridge
import NLA.Proofs.RA10.NuclearNormHomogeneity

/-! RA-10 source Equation (10): exact positive-part trace accounting for the
actual selected compression and both independent supplied spectral bases.
This remains a partial gate toward the frozen transfer Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem trace_spectralMatrix_eq_sum {n : ℕ}
    (eigenvalues : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ a b, ∑ i, Q i a * Q i b = if a = b then 1 else 0) :
    Matrix.trace (NLA.Statements.RA10.SpectralMatrix eigenvalues Q) =
      ∑ a : Fin n, eigenvalues a := by
  simp only [Matrix.trace, Matrix.diag,
    NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  calc
    (∑ i : Fin n, ∑ a : Fin n, eigenvalues a * Q i a * Q i a) =
        ∑ a : Fin n, ∑ i : Fin n, eigenvalues a * Q i a * Q i a :=
      Finset.sum_comm
    _ = ∑ a : Fin n, eigenvalues a * (∑ i : Fin n, Q i a * Q i a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ a : Fin n, eigenvalues a := by
      apply Finset.sum_congr rfl
      intro a _
      have haa : (∑ i : Fin n, Q i a * Q i a) = 1 := by
        simpa using hQ a a
      rw [haa, mul_one]

theorem matchedLeading_compression_excess_positivePart {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    let S_top := ∑ i : Fin n, if i.val < k then eigenvaluesA i else 0
    let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
    let L := S_top - Matrix.trace C
    let e_C := NLA.Statements.RA10.NuclearNorm (A - C) - τ
    e_C = L + 2 * Matrix.trace (hermitianPositivePart (C - A)) := by
  let P := selectedProjection k QAhat
  let C := P * A * P
  let S_top := ∑ i : Fin n, if i.val < k then eigenvaluesA i else 0
  let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
  change NLA.Statements.RA10.NuclearNorm (A - C) - τ =
    (S_top - Matrix.trace C) +
      2 * Matrix.trace (hermitianPositivePart (C - A))
  have hApsd : Matrix.PosSemidef A :=
    (sourcePositiveSemidefinite_iff_mathlibPosSemidef A).mp
      (orderedPSDSpectralDecomposition_positiveSemidefinite hA)
  have hCpsd : Matrix.PosSemidef C := by
    exact selectedCompression_mathlibPosSemidef hA hAhat
  have hM : (C - A).IsHermitian := hCpsd.1.sub hApsd.1
  have hgeneric := nuclearNorm_eq_two_trace_positivePart_sub_trace (C - A) hM
  have hsign : NLA.Statements.RA10.NuclearNorm (A - C) =
      NLA.Statements.RA10.NuclearNorm (C - A) := by
    have hmatrix : A - C = (-1 : ℝ) • (C - A) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hmatrix, nuclearNorm_smul]
    norm_num
  have htraceA : Matrix.trace A = ∑ i : Fin n, eigenvaluesA i := by
    rw [hA.2.2.2]
    exact trace_spectralMatrix_eq_sum eigenvaluesA QA hA.2.2.1
  have hsplit : S_top + τ = ∑ i : Fin n, eigenvaluesA i := by
    dsimp [S_top, τ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k
    · simp [hi, Nat.not_le_of_gt hi]
    · have hki : k ≤ i.val := Nat.le_of_not_gt hi
      simp [hi, hki]
  rw [hsign, hgeneric, Matrix.trace_sub, htraceA]
  linarith

#assert_trust kernel matchedLeading_compression_excess_positivePart
#print axioms matchedLeading_compression_excess_positivePart

end NLA.Proofs.RA10
