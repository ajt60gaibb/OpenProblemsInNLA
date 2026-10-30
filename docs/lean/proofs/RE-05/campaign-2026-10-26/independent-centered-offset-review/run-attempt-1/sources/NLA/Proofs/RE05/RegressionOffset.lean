import NLA.Proofs.RE05.RegressionSolveTransport

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

/-- The literal rhs evaluated on this same plan's true answers to B. -/
def regressionOffset {n q : ℕ} (P : Basis n q) (plan : Plan n) (B : Square n) :
    Fin (q + 1) → ℝ := rhs P plan (planAnswers B plan)

theorem regressionOffset_inner {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (B : Square n) (j : Fin (q + 1)) :
    regressionOffset P plan B j =
      ⟪measurementVector plan (P j), measurementVector plan B⟫_ℝ := by
  rw [regressionOffset, rhs_eq_measurement_inner, observationVector_planAnswers]

theorem regressionOffset_sub {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (A B : Square n) : regressionOffset P plan (A - B) =
      regressionOffset P plan A - regressionOffset P plan B := by
  ext j
  simp only [regressionOffset_inner, Pi.sub_apply]
  change ⟪_, (measurementMap plan) (A - B)⟫_ℝ = _
  rw [map_sub, inner_sub_right]
  rfl

theorem regressionOffset_represent {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) :
    regressionOffset P plan (represent P c) = gram P plan *ᵥ c := by
  ext j
  rw [regressionOffset_inner, gram_mulVec_eq_inner, coefficientMeasurement_apply]

/-- The original plan is fixed throughout. The error coefficients solve the
actual Gram equation with the actual rhs of the true residual answers. -/
theorem singleOutput_residual_equation {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (A : Square n) (c : Fin (q + 1) → ℝ) :
    gram P plan *ᵥ (singleOutput P plan (planAnswers A plan) - c) =
      regressionOffset P plan (A - represent P c) := by
  rw [Matrix.mulVec_sub, singleOutput_normal, regressionOffset_sub,
    regressionOffset_represent]
  rfl

theorem singleOutput_batch_residual_equation {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) (A : Square n)
    (c : Fin (q + 1) → ℝ) :
    gram P (schedule copy) *ᵥ
      (singleOutput P (schedule copy)
        (copyResponses schedule (batchAnswers A schedule) copy) - c) =
      regressionOffset P (schedule copy) (A - represent P c) := by
  rw [copyResponses_batchAnswers]
  exact singleOutput_residual_equation P _ A c

end NLA.Proofs.RE05
