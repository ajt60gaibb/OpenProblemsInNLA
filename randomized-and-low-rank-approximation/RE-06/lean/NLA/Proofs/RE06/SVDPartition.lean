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

def headDiagonal {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (fun j => residualSingularValue C (Fin.castLE hr j))

theorem headEmbedding_diagonal {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) :
    headEmbedding n r hr*headDiagonal C r hr =
      Matrix.diagonal (residualSingularValue C)*headEmbedding n r hr := by
  ext i j
  by_cases h : i=Fin.castLE hr j
  · subst i
    simp [headDiagonal, headEmbedding]
  · simp [headDiagonal, headEmbedding, h]

theorem diagonal_head_tail {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) :
    headEmbedding n r hr*headDiagonal C r hr*(headEmbedding n r hr).transpose +
      tailDiagonal C r = Matrix.diagonal (residualSingularValue C) := by
  rw [headEmbedding_diagonal, Matrix.mul_assoc, headEmbedding_projector]
  ext i j
  simp only [Matrix.diagonal_mul_diagonal, Matrix.add_apply,
    Matrix.diagonal_apply, tailDiagonal]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    split_ifs <;> simp
  · simp [hij]

theorem headEmbedding_isometry {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.transpose*W=1) (r : ℕ) (hr : r ≤ n) :
    (W*headEmbedding n r hr).transpose*(W*headEmbedding n r hr)=1 := by
  calc
    _ = (headEmbedding n r hr).transpose*(W.transpose*W)*headEmbedding n r hr := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hW, Matrix.mul_one, headEmbedding_gram]

theorem residual_svd_partition {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) :
    C = ((exactSVD C).U*headEmbedding n r hr)*headDiagonal C r hr*
        ((exactSVD C).V*headEmbedding n r hr).transpose +
      (exactSVD C).U*tailDiagonal C r*(exactSVD C).V.transpose := by
  conv_lhs => rw [residual_svd_reconstruction C, ← diagonal_head_tail C r hr]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem residual_tail_energy {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    squaredFrobenius (tailDiagonal C r) 0=residualTailEnergy C r := by
  simp [squaredFrobenius, tailDiagonal, Matrix.diagonal_apply,
    residualTailEnergy, residualSpectralHead, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val < r
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem residual_tail_weighted_orthogonal {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) :
    (tailDiagonal C r*(exactSVD C).V.transpose)*
      ((exactSVD C).V*headEmbedding n r hr)=0 := by
  calc
    _ = tailDiagonal C r*((exactSVD C).V.transpose*(exactSVD C).V)*
        headEmbedding n r hr := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [Pseudo.svd_V_gram, Matrix.mul_one, tailDiagonal_head]

#assert_trust kernel headEmbedding_gram
#assert_trust kernel tailDiagonal_head
#assert_trust kernel headEmbedding_projector
#assert_trust kernel headEmbedding_diagonal
#assert_trust kernel diagonal_head_tail
#assert_trust kernel headEmbedding_isometry
#assert_trust kernel residual_svd_partition
#assert_trust kernel residual_tail_energy
#assert_trust kernel residual_tail_weighted_orthogonal
end NLA.Proofs.RE06.Repair
