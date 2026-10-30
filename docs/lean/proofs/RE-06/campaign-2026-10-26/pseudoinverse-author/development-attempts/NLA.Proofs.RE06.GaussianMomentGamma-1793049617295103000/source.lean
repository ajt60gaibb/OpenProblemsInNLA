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
  <;> ring

theorem gamma_inverse_lintegral {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    (∫⁻ x, ENNReal.ofReal x⁻¹ ∂gammaMeasure a r) = ENNReal.ofReal (r / (a - 1)) := by
  have ha1 : 0 < a - 1 := by linarith
  unfold gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have heq : (fun x => gammaPDF a r x * ENNReal.ofReal x⁻¹) =ᵐ[volume]
      (fun x => ENNReal.ofReal (r / (a - 1)) * gammaPDF (a - 1) r x) := by
    filter_upwards [ae_neq (0 : ℝ)] with x hx
    by_cases hxp : 0 < x
    · simp only [gammaPDF]
      rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg (by linarith) hr x),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ r / (a - 1))]
      congr 1
      rw [mul_comm, gammaPDFReal_inverse_weight ha hr hxp]
    · have hxn : x < 0 := by exact lt_of_le_of_ne (le_of_not_gt hxp) hx
      rw [gammaPDF_of_neg hxn, gammaPDF_of_neg hxn]
      simp
  rw [lintegral_congr_ae heq, lintegral_const_mul _ (by fun_prop),
    lintegral_gammaPDF_eq_one ha1 hr, mul_one]

#assert_trust kernel gammaPDFReal_inverse_weight
#assert_trust kernel gamma_inverse_lintegral
#print axioms gamma_inverse_lintegral
end NLA.Proofs.RE06.GaussianMoment
