import NLA.Proofs.RA10.SelectedProjectionIdempotent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.Fin

/-! RA-10: the projector onto the first `k` supplied spectral columns has
rank exactly `k` when `k ≤ n`, including tied and zero eigenvalues. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem selectedProjection_rank {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q)
    (hk : k ≤ n) :
    (selectedProjection k Q).rank = k := by
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal fun a => if a.val < k then 1 else 0
  have hQTQ : Q.transpose * Q = 1 := by
    rcases h with ⟨_, _, hQ, _⟩
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b
  have hdetQ : IsUnit Q.det := Matrix.isUnit_det_of_left_inverse hQTQ
  have hdetQT : IsUnit Q.transpose.det := Q.isUnit_det_transpose hdetQ
  have hrep : selectedProjection k Q = Q * D * Q.transpose := by
    ext i j
    simp only [selectedProjection, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, D]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < k <;> simp [ha]
  rw [hrep]
  calc
    (Q * D * Q.transpose).rank = (Q * D).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det Q.transpose (Q * D) hdetQT
    _ = D.rank := Matrix.rank_mul_eq_right_of_isUnit_det Q D hdetQ
    _ = k := by
      simp only [D, Matrix.rank_diagonal, Fintype.card_subtype]
      have hselector (a : Fin n) :
          (if a.val < k then (1 : ℝ) else 0) ≠ 0 ↔ a.val < k := by
        by_cases ha : a.val < k <;> simp [ha]
      simp only [hselector]
      simp [Fin.card_filter_val_lt, Nat.min_eq_right hk]

#assert_trust kernel selectedProjection_rank
#print axioms selectedProjection_rank

end NLA.Proofs.RA10
