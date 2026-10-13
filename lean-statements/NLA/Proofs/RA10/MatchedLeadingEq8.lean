import NLA.Proofs.RA10.NuclearComplementaryBlocks
import NLA.Proofs.RA10.NuclearNormPSDTrace
import NLA.Proofs.RA10.NuclearPinching
import NLA.Proofs.RA10.NuclearNormHomogeneity
import NLA.Proofs.RA10.MatchedLeadingSupport
import NLA.Proofs.RA10.CustomPSDMathlibBridge

/-! RA-10 source Equation (8): exact excess, selected-compression remainder,
and trace loss accounting for the actual selected projector and both supplied
independent spectral bases. This remains a partial gate toward the Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem trace_spectralMatrix_of_orthonormal_columns {n : ℕ}
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
    _ = ∑ a : Fin n, eigenvalues a *
          (∑ i : Fin n, Q i a * Q i a) := by
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

private theorem trace_complementary_compressions {n : ℕ}
    (P A : Matrix (Fin n) (Fin n) ℝ) (hid : P * P = P) :
    Matrix.trace ((1 - P) * A * (1 - P)) =
      Matrix.trace A - Matrix.trace (P * A * P) := by
  let Q : Matrix (Fin n) (Fin n) ℝ := 1 - P
  have hQid : Q * Q = Q := by
    dsimp [Q]
    noncomm_ring [hid]
  have htraceP : Matrix.trace (P * A * P) = Matrix.trace (P * A) := by
    rw [Matrix.trace_mul_cycle, hid]
  have htraceQ : Matrix.trace (Q * A * Q) = Matrix.trace (Q * A) := by
    rw [Matrix.trace_mul_cycle, hQid]
  calc
    Matrix.trace ((1 - P) * A * (1 - P)) = Matrix.trace (Q * A) := htraceQ
    _ = Matrix.trace ((1 - P) * A) := rfl
    _ = Matrix.trace (A - P * A) := by rw [sub_mul, one_mul]
    _ = Matrix.trace A - Matrix.trace (P * A) := Matrix.trace_sub _ _
    _ = Matrix.trace A - Matrix.trace (P * A * P) := by rw [htraceP]

theorem matchedLeading_excess_ge_remainder_plus_loss {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
      eigenvaluesA QAhat
    let C := P * A * P
    let S_top := ∑ i : Fin n, if i.val < k then eigenvaluesA i else 0
    let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
    let R := NLA.Statements.RA10.NuclearNorm (B₀ - C)
    let L := S_top - Matrix.trace C
    let e₀ := NLA.Statements.RA10.NuclearNorm (A - B₀) - τ
    R + L ≤ e₀ := by
  let P := selectedProjection k QAhat
  let Q : Matrix (Fin n) (Fin n) ℝ := 1 - P
  let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
    eigenvaluesA QAhat
  let C := P * A * P
  let S_top := ∑ i : Fin n, if i.val < k then eigenvaluesA i else 0
  let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
  change NLA.Statements.RA10.NuclearNorm (B₀ - C) +
    (S_top - Matrix.trace C) ≤
      NLA.Statements.RA10.NuclearNorm (A - B₀) - τ
  have hsym : P.transpose = P := selectedProjection_transpose k QAhat
  have hid : P * P = P := selectedProjection_idempotent (k := k) hAhat
  have hQsym : Q.transpose = Q := by simp [Q, hsym]
  have hQid : Q * Q = Q := by
    dsimp [Q]
    noncomm_ring [hid]
  have hPB : P * B₀ * P = B₀ := matchedLeading_supported hA hAhat
  have hPC : P * C * P = C := selectedCompression_supported A hAhat
  have hQBP : Q * P = 0 := by
    dsimp [Q]
    noncomm_ring [hid]
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    noncomm_ring [hid]
  have hQB : Q * B₀ * Q = 0 := by
    calc
      Q * B₀ * Q = Q * (P * B₀ * P) * Q :=
        congrArg (fun Z : Matrix (Fin n) (Fin n) ℝ => Q * Z * Q) hPB.symm
      _ = (Q * P) * B₀ * (P * Q) := by noncomm_ring
      _ = 0 := by rw [hQBP, hPQ]; simp
  have hX : P * (C - B₀) * P = C - B₀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hPC, hPB]
  have hY : (1 - P) * (Q * A * Q) * (1 - P) = Q * A * Q := by
    change Q * (Q * A * Q) * Q = Q * A * Q
    calc
      Q * (Q * A * Q) * Q = (Q * Q) * A * (Q * Q) := by noncomm_ring
      _ = Q * A * Q := by rw [hQid]
  have hpinch : P * (A - B₀) * P + Q * (A - B₀) * Q =
      (C - B₀) + Q * A * Q := by
    have hleft : P * (A - B₀) * P = C - B₀ := by
      calc
        P * (A - B₀) * P = (P * A - P * B₀) * P := by
          rw [Matrix.mul_sub P A B₀]
        _ = P * A * P - P * B₀ * P := by rw [Matrix.sub_mul]
        _ = C - B₀ := by rw [hPB]
    have hright : Q * (A - B₀) * Q = Q * A * Q := by
      calc
        Q * (A - B₀) * Q = (Q * A - Q * B₀) * Q := by
          rw [Matrix.mul_sub Q A B₀]
        _ = Q * A * Q - Q * B₀ * Q := by rw [Matrix.sub_mul]
        _ = Q * A * Q := by rw [hQB, sub_zero]
    rw [hleft, hright]
  have hApsd : Matrix.PosSemidef A :=
    (sourcePositiveSemidefinite_iff_mathlibPosSemidef A).mp
      (orderedPSDSpectralDecomposition_positiveSemidefinite hA)
  have hQpsd : Matrix.PosSemidef (Q * A * Q) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hQsym] using
      hApsd.conjTranspose_mul_mul_same Q
  have hblocks := nuclearNorm_complementary_blocks_add P (C - B₀)
    (Q * A * Q) hsym hid hX hY
  have hpinch_le := nuclearNorm_pinch_le P (A - B₀) hsym hid
  change NLA.Statements.RA10.NuclearNorm
    (P * (A - B₀) * P + Q * (A - B₀) * Q) ≤
      NLA.Statements.RA10.NuclearNorm (A - B₀) at hpinch_le
  rw [hpinch, hblocks, nuclearNorm_eq_trace_of_posSemidef _ hQpsd]
    at hpinch_le
  have hsign : NLA.Statements.RA10.NuclearNorm (C - B₀) =
      NLA.Statements.RA10.NuclearNorm (B₀ - C) := by
    have hmatrix : C - B₀ = (-1 : ℝ) • (B₀ - C) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hmatrix, nuclearNorm_smul]
    norm_num
  have htracecomp : Matrix.trace (Q * A * Q) =
      Matrix.trace A - Matrix.trace C := by
    simpa only [Q, C, P] using trace_complementary_compressions P A hid
  have htraceA : Matrix.trace A = ∑ i : Fin n, eigenvaluesA i := by
    rw [hA.2.2.2]
    exact trace_spectralMatrix_of_orthonormal_columns eigenvaluesA QA hA.2.2.1
  have hsplit : S_top + τ = ∑ i : Fin n, eigenvaluesA i := by
    dsimp [S_top, τ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k
    · simp [hi, Nat.not_le_of_gt hi]
    · have hki : k ≤ i.val := Nat.le_of_not_gt hi
      simp [hi, hki]
  rw [hsign, htracecomp, htraceA] at hpinch_le
  linarith

#assert_trust kernel trace_spectralMatrix_of_orthonormal_columns
#assert_trust kernel trace_complementary_compressions
#assert_trust kernel matchedLeading_excess_ge_remainder_plus_loss
#print axioms matchedLeading_excess_ge_remainder_plus_loss

end NLA.Proofs.RA10
