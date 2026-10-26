import NLA.Statements.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory

/-- All scalar Gaussian monomials are integrable, including the constant. -/
theorem gaussian_power_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_pow] using
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (p := k) (by simp)).integrable_norm_pow'

theorem gaussian_first_integral : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 :=
  integral_id_gaussianReal

theorem gaussian_second_integral : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h : Var[fun x : ℝ => x; gaussianReal 0 1] = 1 := by simp
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero] using h

/-- Coordinate monomials under the actual finite independent Gaussian law. -/
theorem gaussian_product_powers_integrable {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ k i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
  Integrable.fintype_prod (fun i => gaussian_power_integrable (k i))

theorem gaussian_product_powers_integral {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ k i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, ∫ x : ℝ, x ^ k i ∂gaussianReal 0 1 :=
  integral_fintype_prod_eq_prod (fun i (x : ℝ) => x ^ k i)

/-- Symmetry gives the exact third scalar moment. -/
theorem gaussian_third_integral : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have h : (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) =
      -(∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) := by
    calc
      _ = ∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1).map (fun x : ℝ => -x) := by rw [hmap]
      _ = ∫ x : ℝ, (-x) ^ 3 ∂gaussianReal 0 1 := integral_map (by fun_prop) (by fun_prop)
      _ = ∫ x : ℝ, -(x ^ 3) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by ring)
      _ = _ := integral_neg _
  linarith

private theorem gaussian_mgf_deriv_one (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
  exact ((((hasDerivAt_id t).pow 2).div_const 2).exp).congr_deriv (by dsimp; ring)

private theorem gaussian_mgf_deriv_two (t : ℝ) :
    HasDerivAt (fun x : ℝ => x * Real.exp (x ^ 2 / 2))
      ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
  exact ((hasDerivAt_id t).mul (gaussian_mgf_deriv_one t)).congr_deriv (by dsimp; ring)

private theorem gaussian_mgf_deriv_three (t : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x ^ 2) * Real.exp (x ^ 2 / 2))
      ((3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) t := by
  exact ((((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2)).mul
    (gaussian_mgf_deriv_one t))).congr_deriv (by dsimp; ring)

private theorem gaussian_mgf_deriv_four (t : ℝ) :
    HasDerivAt (fun x : ℝ => (3 * x + x ^ 3) * Real.exp (x ^ 2 / 2))
      ((3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) t := by
  exact (((((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)).mul
    (gaussian_mgf_deriv_one t))).congr_deriv (by dsimp; ring)

/-- The exact fourth moment of the original standard real Gaussian. -/
theorem gaussian_fourth_integral : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have hm : mgf (fun x : ℝ => x) (gaussianReal 0 1) =
      (fun t : ℝ => Real.exp (t ^ 2 / 2)) := by
    rw [mgf_fun_id_gaussianReal]
    simp
  have h1 : deriv (fun x : ℝ => Real.exp (x ^ 2 / 2)) =
      (fun t => t * Real.exp (t ^ 2 / 2)) := funext fun t => (gaussian_mgf_deriv_one t).deriv
  have h2 : deriv (fun x : ℝ => x * Real.exp (x ^ 2 / 2)) =
      (fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) :=
    funext fun t => (gaussian_mgf_deriv_two t).deriv
  have h3 : deriv (fun x : ℝ => (1 + x ^ 2) * Real.exp (x ^ 2 / 2)) =
      (fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) :=
    funext fun t => (gaussian_mgf_deriv_three t).deriv
  have h4 : deriv (fun x : ℝ => (3 * x + x ^ 3) * Real.exp (x ^ 2 / 2)) =
      (fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) :=
    funext fun t => (gaussian_mgf_deriv_four t).deriv
  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 3 := by
      rw [hm, show (4 : ℕ) = ((1 + 1) + 1) + 1 from rfl,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_one, h1, h2, h3, h4]
      norm_num

#assert_trust kernel gaussian_power_integrable
#assert_trust kernel gaussian_first_integral
#assert_trust kernel gaussian_second_integral
#assert_trust kernel gaussian_product_powers_integrable
#assert_trust kernel gaussian_product_powers_integral
#assert_trust kernel gaussian_third_integral
#assert_trust kernel gaussian_fourth_integral
#print axioms gaussian_power_integrable
#print axioms gaussian_first_integral
#print axioms gaussian_second_integral
#print axioms gaussian_product_powers_integrable
#print axioms gaussian_product_powers_integral
#print axioms gaussian_third_integral
#print axioms gaussian_fourth_integral
end NLA.Proofs.RE05
