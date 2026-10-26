import NLA.Proofs.RE06.GaussianResidualTails
import NLA.Proofs.RE06.WeightedRangeFinder
import NLA.Proofs.RE06.ActualProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery
open scoped BigOperators

def headEmbedding (n r : ℕ) (hr : r ≤ n) : Matrix (Fin n) (Fin r) ℝ :=
  fun i j => if i = Fin.castLE hr j then 1 else 0

theorem headEmbedding_gram (n r : ℕ) (hr : r ≤ n) :
    (headEmbedding n r hr).transpose*headEmbedding n r hr=1 := by
  ext i j
  simp [headEmbedding, Matrix.mul_apply, Matrix.one_apply, eq_comm]

def tailDiagonal {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i.val < r then 0 else residualSingularValue C i)

theorem tailDiagonal_head {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) : tailDiagonal C r * headEmbedding n r hr=0 := by
  ext i j
  by_cases h : i = Fin.castLE hr j
  · subst i
    simp [tailDiagonal, headEmbedding, j.isLt]
  · simp [tailDiagonal, headEmbedding, h]

/-- The literal head-coordinate projector. -/
theorem headEmbedding_projector (n r : ℕ) (hr : r ≤ n) :
    headEmbedding n r hr*(headEmbedding n r hr).transpose =
      Matrix.diagonal (fun i : Fin n => if i.val < r then (1:ℝ) else 0) := by
  ext i j
  by_cases hi : i.val < r
  · let ii : Fin r := ⟨i.val, hi⟩
    have he : Fin.castLE hr ii = i := Fin.ext rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single ii]
    · simp [headEmbedding, he, Matrix.diagonal_apply, hi, eq_comm]
    · intro b _ hb
      have hne : i ≠ Fin.castLE hr b := by
        intro h
        apply hb
        apply Fin.ext
        exact (congrArg Fin.val h).symm
      simp [headEmbedding, hne]
    · intro h
      exact (h (Finset.mem_univ ii)).elim
  · have hne : ∀ b : Fin r, i ≠ Fin.castLE hr b := by
      intro b h
      exact hi (by simpa only [h, Fin.val_castLE] using b.isLt)
    simp [Matrix.mul_apply, headEmbedding, hne, Matrix.diagonal_apply, hi]

#assert_trust kernel headEmbedding_gram
#assert_trust kernel tailDiagonal_head
#assert_trust kernel headEmbedding_projector
end NLA.Proofs.RE06.Repair
