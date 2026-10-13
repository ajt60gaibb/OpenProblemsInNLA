import NLA.Proofs.RA10.SelectedCompressionOrderedSpectral
import NLA.Proofs.RA10.SelectedProjectionRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Fin

/-! RA-10 source Equation (11): an arbitrary ordered spectral witness for the
actual selected compression has zero eigenvalues beyond its rank-k support.
This is a partial dependency, with all supplied eigenbases retained. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem spectralMatrix_factor {n : ℕ}
    (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix d Q =
      Q * Matrix.diagonal d * Q.transpose := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem selectedCompression_rank_le {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    (selectedProjection k QAhat * A * selectedProjection k QAhat).rank ≤ k := by
  calc
    (selectedProjection k QAhat * A * selectedProjection k QAhat).rank ≤
        (selectedProjection k QAhat * A).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (selectedProjection k QAhat).rank := Matrix.rank_mul_le_left _ _
    _ = k := selectedProjection_rank hAhat hk

private theorem orderedPSD_rank_eq_card_nonzero {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C d Q) :
    C.rank = (Finset.univ.filter fun i : Fin n => d i ≠ 0).card := by
  have hQTQ : Q.transpose * Q = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hC.2.2.1 a b
  have hdetQ : IsUnit Q.det := Matrix.isUnit_det_of_left_inverse hQTQ
  have hdetQT : IsUnit Q.transpose.det := Q.isUnit_det_transpose hdetQ
  rw [hC.2.2.2, spectralMatrix_factor]
  calc
    (Q * Matrix.diagonal d * Q.transpose).rank =
        (Q * Matrix.diagonal d).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det Q.transpose (Q * Matrix.diagonal d) hdetQT
    _ = (Matrix.diagonal d).rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det Q (Matrix.diagonal d) hdetQ
    _ = (Finset.univ.filter fun i : Fin n => d i ≠ 0).card := by
      simp [Matrix.rank_diagonal, Fintype.card_subtype]

theorem selectedCompression_eigenvalues_tail_zero {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (i : Fin n) (hi : k ≤ i.val) :
    eigenvaluesC i = 0 := by
  classical
  by_contra hzero
  have hpos : 0 < eigenvaluesC i :=
    lt_of_le_of_ne (hC.1 i) (Ne.symm hzero)
  have hprefix : (Finset.univ.filter fun b : Fin n => b.val < i.val + 1) ⊆
      (Finset.univ.filter fun b : Fin n => eigenvaluesC b ≠ 0) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    have hbi : b ≤ i := Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp hb)
    have hbpos : 0 < eigenvaluesC b :=
      lt_of_lt_of_le hpos (hC.2.1 hbi)
    exact ne_of_gt hbpos
  have hcard : i.val + 1 ≤
      (Finset.univ.filter fun b : Fin n => eigenvaluesC b ≠ 0).card := by
    have hle := Finset.card_le_card hprefix
    simpa only [Fin.card_filter_val_lt,
      Nat.min_eq_right (Nat.succ_le_of_lt i.isLt)] using hle
  have hrank :
      (Finset.univ.filter fun b : Fin n => eigenvaluesC b ≠ 0).card ≤ k := by
    rw [← orderedPSD_rank_eq_card_nonzero hC]
    exact selectedCompression_rank_le hk hAhat
  omega

theorem selectedCompression_trace_prefix {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    Matrix.trace (selectedProjection k QAhat * A * selectedProjection k QAhat) =
      ∑ i : Fin n, if i.val < k then eigenvaluesC i else 0 := by
  have hQTQ : QC.transpose * QC = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hC.2.2.1 a b
  have htrace : Matrix.trace
      (selectedProjection k QAhat * A * selectedProjection k QAhat) =
      ∑ i : Fin n, eigenvaluesC i := by
    rw [hC.2.2.2, spectralMatrix_factor, Matrix.trace_mul_cycle,
      hQTQ, one_mul, Matrix.trace_diagonal]
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp [hi]
  · have hki : k ≤ i.val := Nat.le_of_not_gt hi
    rw [selectedCompression_eigenvalues_tail_zero hk hAhat hC i hki]
    simp [hi]

#assert_trust kernel selectedCompression_eigenvalues_tail_zero
#assert_trust kernel selectedCompression_trace_prefix
#print axioms selectedCompression_trace_prefix

end NLA.Proofs.RA10
