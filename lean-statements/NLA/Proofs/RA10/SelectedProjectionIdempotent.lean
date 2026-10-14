import NLA.Proofs.RA10.SelectedProjectionBasic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! RA-10: the first `k` columns of the supplied frozen eigenbasis form
an exact idempotent projection, including ties and selected zero eigenvalues.
The rank and supported functional-calculus bridges follow separately. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private def selectorDiagonal {n : ℕ} (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun a => if a.val < k then 1 else 0

private theorem selectedProjection_eq_diagonal {n : ℕ}
    (k : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    selectedProjection k Q = Q * selectorDiagonal k * Q.transpose := by
  ext i j
  simp only [selectedProjection, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, selectorDiagonal]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val < k <;> simp [ha]

private theorem frozenColumns_transpose_mul {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    Q.transpose * Q = 1 := by
  rcases h with ⟨_, _, hQ, _⟩
  ext a b
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b

private theorem selectorDiagonal_mul_self {n k : ℕ} :
    selectorDiagonal (n := n) k * selectorDiagonal k = selectorDiagonal k := by
  unfold selectorDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases ha : a.val < k <;> simp [ha]

theorem selectedProjection_idempotent {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    selectedProjection k Q * selectedProjection k Q = selectedProjection k Q := by
  let D := selectorDiagonal (n := n) k
  have hQTQ : Q.transpose * Q = 1 := frozenColumns_transpose_mul h
  have hDD : D * D = D := selectorDiagonal_mul_self
  rw [selectedProjection_eq_diagonal]
  calc
    (Q * D * Q.transpose) * (Q * D * Q.transpose)
        = Q * D * (Q.transpose * Q) * D * Q.transpose := by
            simp only [Matrix.mul_assoc]
    _ = Q * D * Q.transpose := by
      rw [hQTQ]
      simp [hDD, Matrix.mul_assoc]

#assert_trust kernel selectedProjection_idempotent
#print axioms selectedProjection_idempotent

end NLA.Proofs.RA10
