import NLA.Proofs.RE06.GaussianStream

/-! Quadratic, rather than linear, exponential transforms of the actual
standard real Gaussian law. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace NLA.Proofs.RE06

/-- The real quadratic Gaussian MGF on its genuine finite domain. -/
theorem gaussian_square_exp_integral (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    (∫ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (t * x ^ 2)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-((1 - 2 * t) / 2) * x ^ 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
          mul_assoc, ← Real.exp_add]
        congr 2
        ring)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / ((1 - 2 * t) / 2)) := by rw [integral_gaussian]
    _ = (Real.sqrt (1 - 2 * t))⁻¹ := by
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
        ← Real.sqrt_inv]
      congr 1
      have hp : Real.pi ≠ 0 := Real.pi_ne_zero
      have ht' : 1 - 2 * t ≠ 0 := by linarith
      field_simp
      <;> ring

/-- Integrability follows from the evaluated positive Gaussian integral. -/
theorem gaussian_square_exp_integrable (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  by_contra h
  have he := gaussian_square_exp_integral t ht
  rw [integral_undef h] at he
  have hp : 0 < Real.sqrt (1 - 2 * t) := Real.sqrt_pos.mpr (by linarith)
  exact (inv_ne_zero hp.ne').symm he

/-- Negative quadratic Laplace transform, including zero coefficients. -/
theorem gaussian_square_laplace (a : ℝ) (ha : 0 ≤ a) :
    (∫ x : ℝ, Real.exp (-a * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + 2 * a))⁻¹ := by
  simpa only [mul_neg, sub_neg_eq_add] using
    gaussian_square_exp_integral (-a) (by linarith)

theorem gaussian_square_laplace_integrable (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) (gaussianReal 0 1) :=
  gaussian_square_exp_integrable (-a) (by linarith)

#assert_trust kernel gaussian_square_exp_integral
#assert_trust kernel gaussian_square_exp_integrable
#assert_trust kernel gaussian_square_laplace
#assert_trust kernel gaussian_square_laplace_integrable
#print axioms gaussian_square_exp_integral
#print axioms gaussian_square_exp_integrable
#print axioms gaussian_square_laplace
#print axioms gaussian_square_laplace_integrable
end NLA.Proofs.RE06
