import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace NLA.FR05

abbrev OverlapCoordinates := EuclideanSpace ℝ (Fin 8)

/-- Lebesgue integrability, rather than the zero convention for undefined integrals. -/
theorem integrable_overlap_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : OverlapCoordinates ↦ Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := OverlapCoordinates) (b := (c : ℂ)) (by simpa using hc) 0 0
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h.norm

theorem integrable_overlap_quartic_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : OverlapCoordinates ↦ ‖x‖ ^ 4 * Real.exp (-c * ‖x‖ ^ 2)) := by
  apply ((integrable_overlap_gaussian (half_pos hc)).const_mul (2 / (c / 2) ^ 2)).mono'
    (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh := Real.pow_div_factorial_le_exp (c / 2 * ‖x‖ ^ 2)
    (mul_nonneg (half_pos hc).le (sq_nonneg ‖x‖)) 2
  have hpow : ‖x‖ ^ 4 ≤ 2 / (c / 2) ^ 2 * Real.exp (c / 2 * ‖x‖ ^ 2) := by
    have hc2 : 0 < (c / 2) ^ 2 := by positivity
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc2).mpr
    norm_num at hh
    nlinarith only [hh]
  calc
    _ ≤ (2 / (c / 2) ^ 2 * Real.exp (c / 2 * ‖x‖ ^ 2)) *
        Real.exp (-c * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The exact M⁻⁶ rescaling used in Proposition 3.2. -/
theorem overlap_quartic_gaussian_rescale (c : ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-c * m * ‖x‖ ^ 2)) =
      m⁻¹ ^ 6 * ∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-c * ‖x‖ ^ 2) := by
  let f : OverlapCoordinates → ℝ := fun x ↦ ‖x‖ ^ 4 * Real.exp (-c * ‖x‖ ^ 2)
  have hs := Measure.integral_comp_smul_of_nonneg volume f (Real.sqrt m)
    (hR := Real.sqrt_nonneg m)
  have hdim : Module.finrank ℝ OverlapCoordinates = 8 := by simp [OverlapCoordinates]
  have hpoint : (fun x ↦ f (Real.sqrt m • x)) =
      fun x : OverlapCoordinates ↦ m ^ 2 * (‖x‖ ^ 4 * Real.exp (-c * m * ‖x‖ ^ 2)) := by
    funext x
    dsimp [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg m)]
    have hsq := Real.sq_sqrt hm.le
    have hfour : (Real.sqrt m) ^ 4 = m ^ 2 := by nlinarith [sq_nonneg (Real.sqrt m ^ 2 - m)]
    rw [mul_pow, mul_pow, hsq, hfour]
    ring_nf
  rw [hdim, hpoint, integral_const_mul] at hs
  have hs8 : (Real.sqrt m) ^ 8 = m ^ 4 := by
    calc
      _ = ((Real.sqrt m) ^ 2) ^ 4 := by ring
      _ = _ := by rw [Real.sq_sqrt hm.le]
  rw [hs8] at hs
  change m ^ 2 * (∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-c * m * ‖x‖ ^ 2)) =
    (m ^ 4)⁻¹ * (∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-c * ‖x‖ ^ 2)) at hs
  apply (mul_left_cancel₀ (pow_ne_zero 2 hm.ne'))
  calc
    _ = _ := hs
    _ = _ := by
      have hcoeff : (m ^ 4)⁻¹ = m ^ 2 * m⁻¹ ^ 6 := by field_simp
      rw [hcoeff, mul_assoc]

theorem overlap_local_integral_scale (c : ℝ) {m : ℝ} (hm : 0 < m) :
    m ^ 5 * (∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-c * m * ‖x‖ ^ 2)) =
      (∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-c * ‖x‖ ^ 2)) / m := by
  rw [overlap_quartic_gaussian_rescale c hm]
  have hcoef : m ^ 5 * m⁻¹ ^ 6 = m⁻¹ := by field_simp
  rw [← mul_assoc, hcoef]
  ring

end NLA.FR05
