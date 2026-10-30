import NLA.Proofs.RE05.OffsetContraction
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05CenteredOffsetGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix

/-- Literal batch rhs; original plans remain fixed, including their actual G. -/
theorem actual_rhs_centered_quadratics {n q : ℕ} (P : Basis n q)
    (ε : ℝ) (hε : 0 < ε) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n)
    (j : Fin (q + 1))
    (hOrth : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) R = 0) :
    rhs (orthonormalMember P) (plans P ε ω copy)
      (copyResponses (plans P ε ω) (batchAnswers R (plans P ε ω)) copy) j =
      (1 / ((plans P ε ω copy).s : ℝ)) *
        ∑ g : Fin (plans P ε ω copy).s,
          ((∑ a : Fin n, ∑ b : Fin n,
            offsetQuadraticMatrix P (plans P ε ω copy) R j a b *
              (plans P ε ω copy).G a g * (plans P ε ω copy).G b g) -
            (offsetQuadraticMatrix P (plans P ε ω copy) R j).trace) := by
  rw [copyResponses_batchAnswers]
  have hξ : 0 < squaredAccuracy ε := by unfold squaredAccuracy; positivity
  change regressionOffset (orthonormalMember P)
    (makePlan P (squaredAccuracy ε) ω copy) R j = _
  rw [actualResidualOffset_centered P (squaredAccuracy ε) hξ ω copy R j hOrth]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [dot_quadratic_eq_sum]
  rfl

theorem actual_raw_variance_charge {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    (∑ j : Fin (q + 1), 2 *
      (((residualProjection (makePlan P ξ ω copy) * orthonormalMember P j).transpose *
        (residualProjection (makePlan P ξ ω copy) * R)) *
        ((residualProjection (makePlan P ξ ω copy) * orthonormalMember P j).transpose *
          (residualProjection (makePlan P ξ ω copy) * R)).transpose).trace) ≤
      2 * threshold q ξ * (∑ a : Fin n, ∑ b : Fin n, R a b * R a b) :=
  actual_offsetQuadratic_varianceCharge P ξ ω copy R

theorem actual_width_positive {n q : ℕ} (P : Basis n q) (ε : ℝ) (hε : 0 < ε)
    (ω : ℕ → ℝ) (copy : Fin 15) : 0 < (plans P ε ω copy).s :=
  gaussianWidth_positive q (squaredAccuracy ε) (by unfold squaredAccuracy; positivity)

theorem dependent_zero_family_contraction (n q : ℕ) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    let P : Basis n q := fun _ => 0
    (∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)) ≤
        threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R :=
  actual_offsetQuadratic_energy_contraction _ ξ ω copy R

theorem empty_rhs_zero (q : ℕ) (P : Basis 0 q) (ξ : ℝ) (ω : ℕ → ℝ)
    (copy : Fin 15) (R : Square 0) (j : Fin (q + 1)) :
    regressionOffset (orthonormalMember P) (makePlan P ξ ω copy) R j = 0 := by
  simp [regressionOffset, rhs, dot]

end RE05CenteredOffsetGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.measuredLeft_eq_trace
#print axioms NLA.Proofs.RE05.measuredLeft_eq_trace
#assert_trust kernel NLA.Proofs.RE05.measuredLeft_inner_selected
#print axioms NLA.Proofs.RE05.measuredLeft_inner_selected
#assert_trust kernel NLA.Proofs.RE05.measuredLeft_inner_projection
#print axioms NLA.Proofs.RE05.measuredLeft_inner_projection
#assert_trust kernel NLA.Proofs.RE05.dot_mulVec_quadratic
#print axioms NLA.Proofs.RE05.dot_mulVec_quadratic
#assert_trust kernel NLA.Proofs.RE05.dot_quadratic_eq_sum
#print axioms NLA.Proofs.RE05.dot_quadratic_eq_sum
#assert_trust kernel NLA.Proofs.RE05.offsetQuadraticMatrix
#print axioms NLA.Proofs.RE05.offsetQuadraticMatrix
#assert_trust kernel NLA.Proofs.RE05.offsetQuadraticMatrix_trace
#print axioms NLA.Proofs.RE05.offsetQuadraticMatrix_trace
#assert_trust kernel NLA.Proofs.RE05.actualResidualOffset_centered_unscaled
#print axioms NLA.Proofs.RE05.actualResidualOffset_centered_unscaled
#assert_trust kernel NLA.Proofs.RE05.gaussianWidth_positive
#print axioms NLA.Proofs.RE05.gaussianWidth_positive
#assert_trust kernel NLA.Proofs.RE05.actualResidualOffset_centered
#print axioms NLA.Proofs.RE05.actualResidualOffset_centered
#assert_trust kernel NLA.Proofs.RE05.actual_offsetQuadratic_drop_projection
#print axioms NLA.Proofs.RE05.actual_offsetQuadratic_drop_projection
#assert_trust kernel NLA.Proofs.RE05.family_transpose_product_energy
#print axioms NLA.Proofs.RE05.family_transpose_product_energy
#assert_trust kernel NLA.Proofs.RE05.scalar_psd_trace_bound
#print axioms NLA.Proofs.RE05.scalar_psd_trace_bound
#assert_trust kernel NLA.Proofs.RE05.actual_offsetQuadratic_energy_contraction
#print axioms NLA.Proofs.RE05.actual_offsetQuadratic_energy_contraction
#assert_trust kernel NLA.Proofs.RE05.actual_offsetQuadratic_varianceCharge
#print axioms NLA.Proofs.RE05.actual_offsetQuadratic_varianceCharge
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.actual_rhs_centered_quadratics
#print axioms RE05CenteredOffsetGeometryConsumer.actual_rhs_centered_quadratics
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.actual_raw_variance_charge
#print axioms RE05CenteredOffsetGeometryConsumer.actual_raw_variance_charge
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.actual_width_positive
#print axioms RE05CenteredOffsetGeometryConsumer.actual_width_positive
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.dependent_zero_family_contraction
#print axioms RE05CenteredOffsetGeometryConsumer.dependent_zero_family_contraction
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.empty_rhs_zero
#print axioms RE05CenteredOffsetGeometryConsumer.empty_rhs_zero
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_eq
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_eq
#assert_trust kernel NLA.Proofs.RE05.makePlan_offsetQuadraticMatrix_eq
#print axioms NLA.Proofs.RE05.makePlan_offsetQuadraticMatrix_eq
