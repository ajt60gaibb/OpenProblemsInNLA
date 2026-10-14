import NLA.Proofs.RA10.HermitianPositivePartOrder

/-! Positive-part trace bounds by summing quadratic forms in a full
orthonormal eigenbasis. No optimisation over projectors is needed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open scoped BigOperators

namespace NLA.Proofs.RA10

theorem trace_eq_sum_orthogonal_quadratic {n : ℕ}
    (T Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose * Q = 1) :
    Matrix.trace T = ∑ i : Fin n,
      (fun j => Q j i) ⬝ᵥ (T *ᵥ (fun j => Q j i)) := by
  have hQQ : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQ
  calc
    Matrix.trace T = Matrix.trace (Q.transpose * T * Q) := by
      rw [Matrix.trace_mul_cycle, hQQ, one_mul]
    _ = _ := by
      rw [mul_assoc]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
        dotProduct, Matrix.mulVec]

theorem hermitianPositivePart_trace_eq_sum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Matrix.trace (hermitianPositivePart M) = ∑ i : Fin n, max (hM.eigenvalues i) 0 := by
  have hU := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hUtU : (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose *
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hU
  rw [hermitianPositivePart, dif_pos hM, Matrix.trace_mul_cycle, hUtU, one_mul,
    Matrix.trace_diagonal]

/-- A quadratic majorant on each positive eigenvector controls the trace.
Nonpositive eigenvalues contribute zero and use only positivity of T. -/
theorem hermitianPositivePart_trace_le_of_eigenvector_bound {n : ℕ}
    (M T : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hT : T.PosSemidef)
    (hbound : ∀ i : Fin n, 0 < hM.eigenvalues i →
      hM.eigenvalues i ≤ (fun j => hM.eigenvectorUnitary j i) ⬝ᵥ
        (T *ᵥ (fun j => hM.eigenvectorUnitary j i))) :
    Matrix.trace (hermitianPositivePart M) ≤ Matrix.trace T := by
  have hUtU : (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose *
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hM.eigenvectorUnitary
  rw [hermitianPositivePart_trace_eq_sum M hM,
    trace_eq_sum_orthogonal_quadratic T _ hUtU]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hi : 0 < hM.eigenvalues i
  · rw [max_eq_left hi.le]
    exact hbound i hi
  · rw [max_eq_right (le_of_not_gt hi)]
    simpa only [star_trivial] using
      hT.dotProduct_mulVec_nonneg (fun j => hM.eigenvectorUnitary j i)

#assert_trust kernel trace_eq_sum_orthogonal_quadratic
#assert_trust kernel hermitianPositivePart_trace_eq_sum
#assert_trust kernel hermitianPositivePart_trace_le_of_eigenvector_bound
#print axioms hermitianPositivePart_trace_le_of_eigenvector_bound

end NLA.Proofs.RA10
