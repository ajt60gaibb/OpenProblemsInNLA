import NLA.FR05.Gaussian.GaussianFrameRows
import Mathlib.Probability.Distributions.Exponential

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace NLA.FR05

theorem integral_pair_radius (f : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, f ((p.1 ^ 2 + p.2 ^ 2) / 2)) =
      2 * Real.pi * ∫ s in Ioi (0 : ℝ), f s := by
  have hs : (∫ r in Ioi (0 : ℝ), r * f (r ^ 2 / 2)) =
      ∫ s in Ioi (0 : ℝ), f s := by
    have h := integral_comp_rpow_Ioi (fun s : ℝ ↦ f (s / 2)) (by norm_num : (2 : ℝ) ≠ 0)
    norm_num [Real.rpow_two, smul_eq_mul] at h
    have hc := integral_comp_mul_left_Ioi f 0 (by norm_num : (0 : ℝ) < 1 / 2)
    norm_num [smul_eq_mul] at hc
    have hh : (∫ r in Ioi (0 : ℝ), 2 * r * f (r ^ 2 / 2)) =
        2 * ∫ r in Ioi (0 : ℝ), r * f (r ^ 2 / 2) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    rw [hh] at h
    have he : (fun s : ℝ ↦ f (s / 2)) = fun s ↦ f (1 / 2 * s) := by
      funext s; congr 1; ring
    rw [he, hc] at h
    linarith
  calc
    _ = ∫ p in polarCoord.target, p.1 * f (p.1 ^ 2 / 2) := by
      rw [← integral_comp_polarCoord_symm]
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      simp only [polarCoord_symm_apply, smul_eq_mul]
      congr 2
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    _ = (∫ r in Ioi (0 : ℝ), r * f (r ^ 2 / 2)) *
        ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul]
      simp [polarCoord_target, Measure.volume_eq_prod]
    _ = _ := by
      rw [hs]
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        univ_inter, smul_eq_mul, mul_one]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      ring

theorem integral_expMeasure_one (f : ℝ → ℝ) :
    (∫ s, f s ∂expMeasure 1) = ∫ s in Ioi (0 : ℝ), Real.exp (-s) * f s := by
  change (∫ s, f s ∂volume.withDensity (fun s ↦ ENNReal.ofReal (gammaPDFReal 1 1 s))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal 1 1).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg (a := 1) (r := 1) (by norm_num)
    (by norm_num) _), smul_eq_mul]
  have he (s : ℝ) : gammaPDFReal 1 1 s * f s =
      (Ici (0 : ℝ)).indicator (fun s ↦ Real.exp (-s) * f s) s := by
    simp [gammaPDFReal, Set.indicator, Real.Gamma_one]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem integral_gaussian_pair_radius (f : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, f ((p.1 ^ 2 + p.2 ^ 2) / 2)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = ∫ s, f s ∂expMeasure 1 := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.mul_lt_top
        (by simp [gaussianPDF]) (by simp [gaussianPDF]))]
  simp only [ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul]
  have he (p : ℝ × ℝ) :
      gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2 *
        f ((p.1 ^ 2 + p.2 ^ 2) / 2) =
      (2 * Real.pi)⁻¹ * (Real.exp (-((p.1 ^ 2 + p.2 ^ 2) / 2)) *
        f ((p.1 ^ 2 + p.2 ^ 2) / 2)) := by
    rw [gaussian_real_pair_pdf, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul, ← Measure.volume_eq_prod, integral_pair_radius (fun s ↦ Real.exp (-s) * f s), integral_expMeasure_one]
  field_simp [Real.pi_ne_zero]

theorem gaussian_pair_radius_law :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 ^ 2 + p.2 ^ 2) / 2) = expMeasure 1 := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
  exact integral_gaussian_pair_radius f

theorem gaussian_finTwo_radius_law :
    (Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)).map
      (fun x ↦ (x 0 ^ 2 + x 1 ^ 2) / 2) = expMeasure 1 := by
  have h := (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ gaussianReal 0 1)).map_eq
  rw [← gaussian_pair_radius_law, ← h,
    Measure.map_map (by fun_prop) (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable]
  rfl

theorem normSq_standardComplexTail {n : ℕ} (x : (Fin n × Fin 2) → ℝ) (j : Fin n) :
    Complex.normSq (standardComplexTail x j) = (x (j, 0) ^ 2 + x (j, 1) ^ 2) / 2 := by
  rw [standardComplexTail, Complex.normSq_add_mul_I]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith

theorem standardComplexGaussianTail_map_normSq (n : ℕ) :
    (standardComplexGaussianTail n).map (fun z ↦ fun j ↦ Complex.normSq (z j)) =
      Measure.pi (fun _ : Fin n ↦ expMeasure 1) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  unfold standardComplexGaussianTail
  rw [Measure.map_map (by fun_prop) measurable_standardComplexGaussianTail_map,
    ← map_pi_uncurry (I := Fin n) (J := Fin 2), Measure.map_map
      ((show Measurable (fun z : Signal n ↦ fun j ↦ Complex.normSq (z j)) by fun_prop).comp
        measurable_standardComplexGaussianTail_map) (by fun_prop)]
  have he : ((fun z : Signal n ↦ fun j ↦ Complex.normSq (z j)) ∘ standardComplexTail) ∘
      (fun a (p : Fin n × Fin 2) ↦ a p.1 p.2) =
      fun a : Fin n → Fin 2 → ℝ ↦ fun j ↦ (a j 0 ^ 2 + a j 1 ^ 2) / 2 := by
    funext a j
    exact normSq_standardComplexTail _ _
  rw [he, Measure.pi_map_pi (f := fun _ : Fin n ↦ fun x : Fin 2 → ℝ ↦ (x 0 ^ 2 + x 1 ^ 2) / 2)
    (fun _ ↦ by fun_prop)]
  simp_rw [gaussian_finTwo_radius_law]

theorem standardComplexGaussianTail_map_normSq_pair :
    (standardComplexGaussianTail 2).map
      (fun z ↦ (Complex.normSq (z 0), Complex.normSq (z 1))) =
        (expMeasure 1).prod (expMeasure 1) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have h := (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ expMeasure 1)).map_eq
  rw [← h, ← standardComplexGaussianTail_map_normSq,
    Measure.map_map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable (by fun_prop)]
  rfl

end NLA.FR05
