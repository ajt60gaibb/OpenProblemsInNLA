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
  simp [headEmbedding, Matrix.mul_apply, Matrix.one_apply]

def tailDiagonal {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i.val < r then 0 else residualSingularValue C i)

theorem tailDiagonal_head {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) : tailDiagonal C r * headEmbedding n r hr=0 := by
  ext i j
  simp only [tailDiagonal, Matrix.diagonal_mul, headEmbedding, Matrix.zero_apply]
  split_ifs with h h'
  · simp
  · subst i
    exact (not_lt_of_ge (le_of_not_gt h) j.isLt).elim
  · simp
  · simp

#assert_trust kernel headEmbedding_gram
#assert_trust kernel tailDiagonal_head
end NLA.Proofs.RE06.Repair
