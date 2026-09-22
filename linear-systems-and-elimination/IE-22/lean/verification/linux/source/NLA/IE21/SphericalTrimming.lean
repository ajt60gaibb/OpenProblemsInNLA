import NLA.IE21.PopulationTrimming
import NLA.IE21.SphericalMoments

/-!
The exact spherical-to-Gaussian lower-tail comparison from the frozen IE-21
boundary. The coupling uses the actual normalized surface law and the proved
Gaussian radius-direction independence, with no asymptotic law assumptions.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

/-- Cauchy--Schwarz for the first absolute moment on a probability space. -/
theorem integral_abs_le_sqrt_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) (hF2 : Integrable (fun ω => F ω ^ 2) μ) :
    (∫ ω, |F ω| ∂μ) ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := by
  have hm : MemLp F 2 μ := (memLp_two_iff_integrable_sq hF).2 hF2
  have hv := variance_nonneg (fun ω => |F ω|) μ
  rw [variance_eq_sub (show MemLp (fun ω => |F ω|) 2 μ from hm.abs)] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  apply Real.le_sqrt_of_sq_le
  linarith

/-- The exact normalized radial variance bound, with the source constant sqrt(2/n). -/
theorem gaussian_radius_deviation_bound (n : ℕ) (hn : 1 ≤ n) :
    (∫ g : Space n, |1 - ‖g‖ ^ 2 / n| ∂stdGaussian (Space n)) ≤
      Real.sqrt (2 / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc : Integrable (fun g : Space n => (‖g‖ ^ 2 - n) ^ 2) (stdGaussian (Space n)) := by
    have hi : Integrable (fun g : Space n => ‖g‖ ^ 4 - (2 * (n : ℝ)) * ‖g‖ ^ 2 + (n : ℝ) ^ 2) (stdGaussian (Space n)) := ((gaussian_norm_pow_integrable n 4).sub
      ((gaussian_norm_pow_integrable n 2).const_mul (2 * n))).add
        (integrable_const ((n : ℝ) ^ 2))
    apply hi.congr
    filter_upwards with g
    ring
  have heq (g : Space n) : (1 - ‖g‖ ^ 2 / n) ^ 2 = (‖g‖ ^ 2 - n) ^ 2 / (n : ℝ) ^ 2 := by
    field_simp
    ring
  have hF2 : Integrable (fun g : Space n => (1 - ‖g‖ ^ 2 / n) ^ 2)
      (stdGaussian (Space n)) := by
    simp_rw [heq]
    exact hc.div_const _
  have hmoment : (∫ g : Space n, (1 - ‖g‖ ^ 2 / n) ^ 2 ∂stdGaussian (Space n)) =
      2 / (n : ℝ) := by
    simp_rw [heq]
    rw [integral_div, gaussian_norm_sq_centered_moment n hn]
    field_simp
  have h := integral_abs_le_sqrt_second_moment (stdGaussian (Space n))
    (fun g : Space n => 1 - ‖g‖ ^ 2 / n) (by fun_prop) hF2
  rwa [hmoment] at h

/-- The exact mean absolute error in the Gaussian-direction coupling reduces
to the normalized radial deviation. -/
theorem spherical_gaussian_coupling_distance (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) :
    (∫ g : Space n, |directionalEnergy x (gaussianDirection g) - (inner ℝ g x) ^ 2|
      ∂stdGaussian (Space n)) ≤ Real.sqrt (2 / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpoint (g : Space n) :
      |directionalEnergy x (gaussianDirection g) - (inner ℝ g x) ^ 2| =
        |1 - ‖g‖ ^ 2 / n| * directionalEnergy x (gaussianDirection g) := by
    have hi : inner ℝ g x = ‖g‖ * inner ℝ (gaussianDirection g) x := by
      rw [← real_inner_smul_left, norm_smul_gaussianDirection]
    have hy : 0 ≤ directionalEnergy x (gaussianDirection g) := by
      unfold directionalEnergy
      positivity
    have hid : directionalEnergy x (gaussianDirection g) - (inner ℝ g x) ^ 2 =
        (1 - ‖g‖ ^ 2 / n) * directionalEnergy x (gaussianDirection g) := by
      rw [hi]
      unfold directionalEnergy
      field_simp
    rw [hid, abs_mul, abs_of_nonneg hy]
  simp_rw [hpoint]
  have hfac := (gaussian_radius_direction_independent n hn).integral_fun_comp_mul_comp
    (f := fun r : ℝ => |1 - r ^ 2 / n|)
    (g := directionalEnergy x)
    measurable_norm.aemeasurable (measurable_gaussianDirection n).aemeasurable
    (by fun_prop) (by unfold directionalEnergy; fun_prop)
  rw [hfac]
  have hmean : (∫ g : Space n, directionalEnergy x (gaussianDirection g)
      ∂stdGaussian (Space n)) = 1 := by
    rw [← integral_map (measurable_gaussianDirection n).aemeasurable
      (show AEStronglyMeasurable (directionalEnergy x)
        ((stdGaussian (Space n)).map gaussianDirection) by unfold directionalEnergy; fun_prop),
      gaussian_direction_law n hn, directionalEnergy_mean n hn x hx]
  rw [hmean, mul_one]
  exact gaussian_radius_deviation_bound n hn

/-- Exact frozen target, using the literal surface measure and canonical Gaussian integral. -/
theorem spherical_gaussian_trimming (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (n : ℕ) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1) :
    |populationTrim θ (sphereLaw n) (directionalEnergy x) - gaussianTrim θ| ≤
      Real.sqrt (2 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hY : Integrable (fun g : Space n => directionalEnergy x (gaussianDirection g))
      (stdGaussian (Space n)) := by
    have h := directionalEnergy_integrable n hn1 x hx
    rw [← gaussian_direction_law n hn1] at h
    exact h.comp_aemeasurable (measurable_gaussianDirection n).aemeasurable
  have hZ : Integrable (fun g : Space n => (inner ℝ g x) ^ 2) (stdGaussian (Space n)) := by
    have h := gaussian_square_integrable
    rw [← gaussian_projection_law x hx] at h
    simpa only [Function.comp_def, real_inner_comm] using h.comp_aemeasurable (by fun_prop)
  have hYpop := populationTrim_map (μ := stdGaussian (Space n)) (θ := θ)
    gaussianDirection (measurable_gaussianDirection n).aemeasurable
    (directionalEnergy x) (by unfold directionalEnergy; fun_prop)
  rw [gaussian_direction_law n hn1] at hYpop
  have hZpop := populationTrim_map (μ := stdGaussian (Space n)) (θ := θ)
    (fun g : Space n => inner ℝ x g) (by fun_prop) (fun t : ℝ => t ^ 2) (by fun_prop)
  rw [gaussian_projection_law x hx, populationTrim_gaussian θ hθ] at hZpop
  have heq : (fun g : Space n => (inner ℝ x g) ^ 2) = (fun g => (inner ℝ g x) ^ 2) := by
    funext g
    rw [real_inner_comm]
  rw [heq] at hZpop
  have h := populationTrim_coupling_lipschitz hθ.2.le hY hZ
  rw [← hYpop, ← hZpop] at h
  exact h.trans (spherical_gaussian_coupling_distance n hn1 x hx)

end NLA.IE21
