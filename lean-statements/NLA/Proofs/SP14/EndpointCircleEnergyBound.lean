import NLA.Proofs.SP14.EndpointCircleEnergy

/-!
The explicit conventional full-circle Sobolev energy bound for the actual
endpoint realization, using the audited two-block Fourier operator norm.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Exact conventional `(1+|p|)^(2r)` circle energy bound, with the
literal Schur constant from the actual negative Fourier matrix. -/
theorem endpointCircleEnergy_le_input (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    (∑' p : ℤ, endpointCircleEnergyTerm r
      (endpointCircleRealization r hrHalf hr1 y) p) ≤
      (2 : ℝ) ^ (2 * r) * (1 + endpointSchurConstant r ^ 2) * ‖y‖ ^ 2 := by
  have hr : 0 < r := by linarith
  have henergy := (endpointCircleEnergy_bounds r hrHalf hr1 y).2
  have hnorm := endpointTwoSidedCoeffOperator_apply_norm_le r hr hr1 y
  have hroot_nonneg : 0 ≤ Real.sqrt (1 + endpointSchurConstant r ^ 2) :=
    Real.sqrt_nonneg _
  have hroot_sq : (Real.sqrt (1 + endpointSchurConstant r ^ 2)) ^ 2 =
      1 + endpointSchurConstant r ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm_sq : ‖endpointTwoSidedCoeffOperator r hr hr1 y‖ ^ 2 ≤
      (1 + endpointSchurConstant r ^ 2) * ‖y‖ ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hnorm)
      (add_nonneg
        (mul_nonneg hroot_nonneg (norm_nonneg y))
        (norm_nonneg (endpointTwoSidedCoeffOperator r hr hr1 y)))]
  have hfac : 0 ≤ (2 : ℝ) ^ (2 * r) := by positivity
  calc
    _ ≤ (2 : ℝ) ^ (2 * r) *
          ‖endpointTwoSidedCoeffOperator r hr hr1 y‖ ^ 2 := henergy
    _ ≤ (2 : ℝ) ^ (2 * r) *
          ((1 + endpointSchurConstant r ^ 2) * ‖y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm_sq hfac
    _ = _ := by ring

#assert_trust kernel endpointCircleEnergy_le_input
#print axioms endpointCircleEnergy_le_input

end NLA.Proofs.SP14
