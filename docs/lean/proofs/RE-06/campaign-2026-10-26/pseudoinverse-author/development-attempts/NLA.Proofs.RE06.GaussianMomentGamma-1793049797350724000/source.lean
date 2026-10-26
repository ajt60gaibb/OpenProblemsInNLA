import Mathlib
import LeanCert.Tactic.Verification

/-! A genuine reciprocal Gamma moment. Identifying a projected Gaussian squared
norm with this law is a separate remaining transport obligation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace NLA.Proofs.RE06.GaussianMoment

theorem gammaPDFReal_inverse_weight {a r x : ℝ} (ha : 1 < a) (hr : 0 < r) (hx : 0 < x) :
    x⁻¹ * gammaPDFReal a r x = r / (a - 1) * gammaPDFReal (a - 1) r x := by
  have ha1 : 0 < a - 1 := by linarith
  have hga : Gamma a = (a - 1) * Gamma (a - 1) := by
    simpa using (Real.Gamma_add_one (ne_of_gt ha1))
  have hpr : r ^ a = r ^ (a - 1) * r := by
    calc
      r ^ a = r ^ ((a - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr]; simp
  have hpx : x ^ (a - 1) = x ^ (a - 2) * x := by
    calc
      x ^ (a - 1) = x ^ ((a - 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx]; simp
  have hgpos := Gamma_pos_of_pos ha1
  simp only [gammaPDFReal, if_pos hx.le]
  rw [hga, hpr, hpx]
  have he : a - 1 - 1 = a - 2 := by ring
  rw [he]
  field_simp

theorem gamma_inverse_lintegral {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    (∫⁻ x, ENNReal.ofReal x⁻¹ ∂gammaMeasure a r) = ENNReal.ofReal (r / (a - 1)) := by
  have ha1 : 0 < a - 1 := by linarith
  have hm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hm1 : Measurable (gammaPDF (a - 1) r) :=
    (measurable_gammaPDFReal (a - 1) r).ennreal_ofReal
  unfold gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume hm (by fun_prop)]
  change (∫⁻ x, gammaPDF a r x * ENNReal.ofReal x⁻¹) = ENNReal.ofReal (r / (a - 1))
  have heq : (fun x => gammaPDF a r x * ENNReal.ofReal x⁻¹) =ᵐ[volume]
      (fun x => ENNReal.ofReal (r / (a - 1)) * gammaPDF (a - 1) r x) := by
    have hn : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hn] with x hx
    by_cases hxp : 0 < x
    · simp only [gammaPDF]
      rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg (by linarith) hr x),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ r / (a - 1))]
      exact congrArg ENNReal.ofReal (by
        rw [mul_comm, gammaPDFReal_inverse_weight ha hr hxp])
    · have hxn : x < 0 := by exact lt_of_le_of_ne (le_of_not_gt hxp) hx
      rw [gammaPDF_of_neg hxn, gammaPDF_of_neg hxn]
      simp
  rw [lintegral_congr_ae heq, lintegral_const_mul _ hm1,
    lintegral_gammaPDF_eq_one ha1 hr, mul_one]

theorem gamma_ae_nonneg (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  rw [ae_iff]
  change gammaMeasure a r {x : ℝ | ¬0 ≤ x} = 0
  simp only [not_le]
  change gammaMeasure a r (Set.Iio 0) = 0
  unfold gammaMeasure
  rw [Measure.withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem gamma_inverse_integrable {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x⁻¹) (gammaMeasure a r) := by
  have hn : 0 ≤ᵐ[gammaMeasure a r] (fun x : ℝ => x⁻¹) :=
    (gamma_ae_nonneg a r).mono (fun x hx => inv_nonneg.mpr hx)
  refine ⟨(measurable_inv : Measurable (fun x : ℝ => x⁻¹)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hn, gamma_inverse_lintegral ha hr]
  exact ENNReal.ofReal_lt_top

theorem gamma_inverse_integral {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    (∫ x, x⁻¹ ∂gammaMeasure a r) = r / (a - 1) := by
  have hn : 0 ≤ᵐ[gammaMeasure a r] (fun x : ℝ => x⁻¹) :=
    (gamma_ae_nonneg a r).mono (fun x hx => inv_nonneg.mpr hx)
  rw [integral_eq_lintegral_of_nonneg_ae hn (gamma_inverse_integrable ha hr).1,
    gamma_inverse_lintegral ha hr, ENNReal.toReal_ofReal (by positivity)]

#assert_trust kernel gammaPDFReal_inverse_weight
#assert_trust kernel gamma_inverse_lintegral
#assert_trust kernel gamma_inverse_integrable
#assert_trust kernel gamma_inverse_integral
#print axioms gamma_inverse_lintegral
end NLA.Proofs.RE06.GaussianMoment
