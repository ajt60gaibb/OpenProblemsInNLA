import NLA.Proofs.RA10.HermitianPositivePart
import NLA.Proofs.RA10.RidgeScalar
import NLA.Proofs.RA10.SelectedCompressionTail
import NLA.Proofs.RA10.NuclearNormHomogeneity

/-! RA-10 source Equation (13), first equality: exact ridge nuclear excess as
the ridge trace loss plus twice the positive-part trace. This is a partial
gate; the source Lemma 2 inequality and frozen Target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem ridgeTrace_spectralMatrix {n : ℕ}
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

private theorem ridgeTrace_functionMatrix_hermitian {n : ℕ}
    (f : ℝ → ℝ) (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    (NLA.Statements.RA10.FunctionMatrix f d Q).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  intro i j
  simp only [NLA.Statements.RA10.FunctionMatrix,
    NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem matchedLeading_ridge_excess_positivePart_identity {n k : ℕ}
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
    let F_A := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA
    let F_C := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC
    let τ_s := ∑ i : Fin n, if k ≤ i.val then ridgeAtom s (eigenvaluesA i) else 0
    let L_s := (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) -
      Matrix.trace F_C
    NLA.Statements.RA10.NuclearNorm (F_A - F_C) - τ_s =
      L_s + 2 * Matrix.trace (hermitianPositivePart (F_C - F_A)) := by
  let F_A := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA
  let F_C := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC
  let τ_s := ∑ i : Fin n, if k ≤ i.val then ridgeAtom s (eigenvaluesA i) else 0
  let L_s := (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) -
    Matrix.trace F_C
  change NLA.Statements.RA10.NuclearNorm (F_A - F_C) - τ_s =
    L_s + 2 * Matrix.trace (hermitianPositivePart (F_C - F_A))
  have hM : (F_C - F_A).IsHermitian :=
    (ridgeTrace_functionMatrix_hermitian (ridgeAtom s) eigenvaluesC QC).sub
      (ridgeTrace_functionMatrix_hermitian (ridgeAtom s) eigenvaluesA QA)
  have htraceA : Matrix.trace F_A =
      ∑ i : Fin n, ridgeAtom s (eigenvaluesA i) := by
    exact ridgeTrace_spectralMatrix _ QA hA.2.2.1
  have hsplit :
      (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) + τ_s =
        ∑ i : Fin n, ridgeAtom s (eigenvaluesA i) := by
    dsimp [τ_s]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k
    · simp [hi, Nat.not_le_of_gt hi]
    · have hki : k ≤ i.val := Nat.le_of_not_gt hi
      simp [hi, hki]
  have hsign : NLA.Statements.RA10.NuclearNorm (F_A - F_C) =
      NLA.Statements.RA10.NuclearNorm (F_C - F_A) := by
    have hmatrix : F_A - F_C = (-1 : ℝ) • (F_C - F_A) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hmatrix, nuclearNorm_smul]
    norm_num
  have hgeneric := nuclearNorm_eq_two_trace_positivePart_sub_trace (F_C - F_A) hM
  rw [hsign, hgeneric, Matrix.trace_sub, htraceA]
  dsimp [L_s]
  linarith

#assert_trust kernel matchedLeading_ridge_excess_positivePart_identity
#print axioms matchedLeading_ridge_excess_positivePart_identity

end NLA.Proofs.RA10
