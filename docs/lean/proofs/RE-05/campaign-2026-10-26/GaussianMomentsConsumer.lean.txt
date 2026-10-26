import NLA.Proofs.RE05.GaussianMoments
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory NLA.Proofs.RE05

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) :=
  gaussian_power_integrable k
example : (∫ x : ℝ, x ∂gaussianReal 0 1) = 0 := gaussian_first_integral
example : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := gaussian_second_integral
example : (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) = 0 := gaussian_third_integral
example : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := gaussian_fourth_integral
example {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ k i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
  gaussian_product_powers_integrable k
example {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ k i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, ∫ x : ℝ, x ^ k i ∂gaussianReal 0 1 := gaussian_product_powers_integral k

-- This is the same standard Gaussian law as every original stream coordinate.
example (j : ℕ) :
    (∫ ω : ℕ → ℝ, (ω j) ^ 4
      ∂NLA.Computation.NonadaptiveMatrixQuery.GaussianLaw) = 3 := by
  have h := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => gaussianReal 0 1) j).hasLaw.integral_comp
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) by fun_prop)
  simpa only [gaussian_fourth_integral] using h

#assert_trust kernel gaussian_power_integrable
#assert_trust kernel gaussian_first_integral
#assert_trust kernel gaussian_second_integral
#assert_trust kernel gaussian_third_integral
#assert_trust kernel gaussian_fourth_integral
#assert_trust kernel gaussian_product_powers_integrable
#assert_trust kernel gaussian_product_powers_integral
#print axioms gaussian_power_integrable
#print axioms gaussian_first_integral
#print axioms gaussian_second_integral
#print axioms gaussian_third_integral
#print axioms gaussian_fourth_integral
#print axioms gaussian_product_powers_integrable
#print axioms gaussian_product_powers_integral
