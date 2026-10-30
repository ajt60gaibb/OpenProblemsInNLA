import NLA.Proofs.RE05.CenteredOffset

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix

/-- Actual residual frame columns already lie in the residual projector. -/
theorem actual_offsetQuadratic_drop_projection {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) (j : Fin (q + 1)) :
    offsetQuadraticMatrix P (makePlan P ξ ω copy) R j =
      (residualBasisBlock P (makePlan P ξ ω copy) j).transpose * R := by
  let plan := makePlan P ξ ω copy
  have hH := makePlan_residualProjection_idempotent P ξ ω copy
  simp only [offsetQuadraticMatrix, residualBasisBlock, Matrix.transpose_mul,
    (residualProjection_symmetric (makePlan P ξ ω copy)).eq]
  change (orthonormalMember P j).transpose * residualProjection plan *
      (residualProjection plan * R) =
    (orthonormalMember P j).transpose * residualProjection plan * R
  calc
    _ = (orthonormalMember P j).transpose *
        ((residualProjection plan * residualProjection plan) * R) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hH]; simp only [Matrix.mul_assoc]; rfl

theorem family_transpose_product_energy {n q : ℕ} (F : Basis n q) (R : Square n) :
    (∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
      ((F j).transpose * R) ((F j).transpose * R)) =
      (R.transpose * (∑ j : Fin (q + 1), F j * (F j).transpose) * R).trace := by
  calc
    _ = ∑ j : Fin (q + 1), (R.transpose * (F j * (F j).transpose) * R).trace := by
      apply Finset.sum_congr rfl
      intro j _
      rw [matrix_inner_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]

theorem scalar_psd_trace_bound {n : ℕ} (S R : Square n) (t : ℝ)
    (hS : (t • (1 : Square n) - S).PosSemidef) :
    (R.transpose * S * R).trace ≤ t * NLA.Computation.LinearFamilyQuery.inner R R := by
  have h := (hS.conjTranspose_mul_mul_same R).trace_nonneg
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul] at h
  rw [← matrix_inner_trace R R] at h
  exact sub_nonneg.mp h

/-- The exact deterministic contraction used in the second moment of the
actual centered rhs. It applies to every actual plan and every residual R. -/
theorem actual_offsetQuadratic_energy_contraction {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    (∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)) ≤
      threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R := by
  simp only [actual_offsetQuadratic_drop_projection]
  rw [family_transpose_product_energy, residualBasisBlock_gram]
  exact scalar_psd_trace_bound _ R _ (makePlan_residualLeverage_bound P ξ ω copy)

/-- Sum of exactly the `2*trace(A*A.transpose)` quantities appearing in the
general real Gaussian quadratic variance bound, with no probability premise. -/
theorem actual_offsetQuadratic_varianceCharge {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    (∑ j : Fin (q + 1), 2 *
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j *
        (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j).transpose).trace) ≤
      2 * threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R := by
  calc
    _ = 2 * ∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
        (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)
        (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [matrix_inner_trace, Matrix.trace_mul_comm]
    _ ≤ 2 * (threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R) :=
      mul_le_mul_of_nonneg_left (actual_offsetQuadratic_energy_contraction P ξ ω copy R)
        (by norm_num)
    _ = _ := by ring

end NLA.Proofs.RE05
