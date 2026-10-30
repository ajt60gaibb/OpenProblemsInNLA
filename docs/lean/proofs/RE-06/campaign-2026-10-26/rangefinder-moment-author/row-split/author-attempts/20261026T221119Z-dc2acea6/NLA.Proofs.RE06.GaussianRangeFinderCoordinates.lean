import NLA.Proofs.RE06.ActualRangeFinder
import NLA.Proofs.RE06.GaussianRowSplit

/-! Pointwise identification of the actual padded SVD tail with the genuine
remaining-row Gaussian block. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

def gaussianWeightedTail {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) : Matrix (Fin n) (Fin (n-r)) ℝ :=
  fun i j => if i = gaussianTailRow n r hr j then residualSingularValue C i else 0

theorem gaussian_tail_row_eq_self {n r : ℕ} (hr : r ≤ n) (i : Fin n) (hi : ¬ i.val < r) :
    gaussianTailRow n r hr (⟨i.val-r, by omega⟩ : Fin (n-r)) = i := by
  apply Fin.ext
  dsimp [gaussianTailRow]
  omega

theorem gaussian_tail_row_injective {n r : ℕ} (hr : r ≤ n) :
    Function.Injective (gaussianTailRow n r hr) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [gaussianTailRow] at hh
  omega

theorem gaussianWeightedTail_energy {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) :
    squaredFrobenius (gaussianWeightedTail C r hr) 0 = residualTailEnergy C r := by
  rw [← Repair.residual_tail_energy C r]
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · have hn (j : Fin (n-r)) : i ≠ gaussianTailRow n r hr j := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [gaussianTailRow] at hh
      omega
    simp [gaussianWeightedTail, hn, Repair.tailDiagonal, hi, Matrix.diagonal_apply]
  · let j : Fin (n-r) := ⟨i.val-r, by omega⟩
    have hj : gaussianTailRow n r hr j = i := gaussian_tail_row_eq_self hr i hi
    have hneq (l : Fin (n-r)) (hl : l ≠ j) : i ≠ gaussianTailRow n r hr l := by
      intro h
      apply hl
      apply gaussian_tail_row_injective hr
      exact h.symm.trans hj.symm
    rw [Finset.sum_eq_single j]
    · simp [gaussianWeightedTail, hj, Repair.tailDiagonal, hi, Matrix.diagonal_apply]
    · intro l _ hl
      simp [gaussianWeightedTail, hneq l hl]
    · intro h
      exact (h (Finset.mem_univ j)).elim

theorem gaussianWeightedTail_mul_entries {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    (x : Fin n × Fin k → ℝ) :
    gaussianWeightedTail C r hr *
        Matrix.of (fun l j => gaussianTailEntries n r k hr x (l,j)) =
      Repair.tailDiagonal C r * Matrix.of (fun i j => x (i,j)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Repair.tailDiagonal,
    Matrix.diagonal_apply]
  by_cases hi : i.val < r
  · have hn (l : Fin (n-r)) : i ≠ gaussianTailRow n r hr l := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [gaussianTailRow] at hh
      omega
    simp [gaussianWeightedTail, hn, hi]
  · let l : Fin (n-r) := ⟨i.val-r, by omega⟩
    have hl : gaussianTailRow n r hr l = i := gaussian_tail_row_eq_self hr i hi
    have hneq (z : Fin (n-r)) (hz : z ≠ l) : i ≠ gaussianTailRow n r hr z := by
      intro h
      apply hz
      apply gaussian_tail_row_injective hr
      exact h.symm.trans hl.symm
    rw [Finset.sum_eq_single l]
    · simp [gaussianWeightedTail, hl, hi, gaussianTailEntries]
    · intro z _ hz
      simp [gaussianWeightedTail, hneq z hz]
    · intro h
      exact (h (Finset.mem_univ l)).elim

theorem gaussian_head_entries_matrix {n k : ℕ} (r : ℕ) (hr : r ≤ n)
    (x : Fin n × Fin k → ℝ) :
    Matrix.of (fun i j => gaussianHeadEntries n r k hr x (i,j)) =
      (Repair.headEmbedding n r hr).transpose * Matrix.of (fun i j => x (i,j)) := by
  ext i j
  simp [Repair.headEmbedding, Matrix.mul_apply, gaussianHeadEntries, eq_comm]

/-- The actual random energy is exactly a two-sided Gaussian product after
splitting the rotated entries into head and tail rows. -/
theorem tailRandomEnergy_eq_split_product {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    (G : Matrix (Fin n) (Fin k) ℝ) :
    Repair.tailRandomEnergy C r hr G = squaredFrobenius
      (gaussianWeightedTail C r hr *
        Matrix.of (fun l j => gaussianTailEntries n r k hr
          (fun p => ((exactSVD C).V.transpose * G) p.1 p.2) (l,j)) *
        pseudoInverse (Matrix.of (fun i j => gaussianHeadEntries n r k hr
          (fun p => ((exactSVD C).V.transpose * G) p.1 p.2) (i,j)))) 0 := by
  rw [gaussianWeightedTail_mul_entries, gaussian_head_entries_matrix]
  unfold Repair.tailRandomEnergy Repair.headCoordinates
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

#assert_trust kernel gaussianWeightedTail
#assert_trust kernel gaussian_tail_row_eq_self
#assert_trust kernel gaussian_tail_row_injective
#assert_trust kernel gaussianWeightedTail_energy
#assert_trust kernel gaussianWeightedTail_mul_entries
#assert_trust kernel gaussian_head_entries_matrix
#assert_trust kernel tailRandomEnergy_eq_split_product
#print axioms gaussianWeightedTail
#print axioms gaussian_tail_row_eq_self
#print axioms gaussian_tail_row_injective
#print axioms gaussianWeightedTail_energy
#print axioms gaussianWeightedTail_mul_entries
#print axioms gaussian_head_entries_matrix
#print axioms tailRandomEnergy_eq_split_product
end NLA.Proofs.RE06
