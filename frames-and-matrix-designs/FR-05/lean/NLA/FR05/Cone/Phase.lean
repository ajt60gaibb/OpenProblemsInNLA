import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Fourier.AddCircle

/-! ## ConePhaseIntegral -/

section

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Metric Real InnerProductSpace
open scoped Real

namespace NLA.FR05

theorem circleAverage_poisson_zero (w : ℂ) (hw : ‖w‖ < 1) :
    circleAverage (poissonKernel 0 w) 0 1 = 1 := by
  have h := (InnerProductSpace.harmonicOnNhd_const (c := (1 : ℝ))
    (s := closedBall (0 : ℂ) 1)).circleAverage_poissonKernel_smul
      (w := w) (by simpa using hw)
  simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, mul_one] using h

theorem poissonKernel_zero_eq (w z : ℂ) (hz : ‖z‖ = 1) :
    poissonKernel 0 w z = (1 - Complex.normSq w) / Complex.normSq (z - w) := by
  simp [poissonKernel, hz, Complex.normSq_eq_norm_sq]

theorem normSq_sub_circle (w z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.normSq (z - w) = 1 + Complex.normSq w - 2 * (star w * z).re := by
  rw [Complex.normSq_sub, hz, mul_comm z]
  rfl

theorem poissonKernel_zero_eq_analytic (w z : ℂ) (hz : ‖z‖ = 1) :
    poissonKernel 0 w z = ((1 + star w * z) / (1 - star w * z)).re := by
  have hz' : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have he : Complex.normSq (1 - star w * z) = Complex.normSq (z - w) := by
    simp [Complex.normSq_sub, Complex.normSq_mul, hz',
      Complex.mul_re, mul_comm]
  have hp := congrFun (poissonKernel_eq_re_herglotzRieszKernel
    (c := 0) (w := star w * z)) 1
  simp only [Function.comp_apply, herglotzRieszKernel, sub_zero] at hp
  simp only [Complex.star_def] at he
  rw [← hp, poissonKernel_zero_eq _ _ (norm_one),
    Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, hz', mul_one, he]
  exact poissonKernel_zero_eq w z hz

theorem circleAverage_poisson_zero_sq (w : ℂ) (hw : ‖w‖ < 1) :
    circleAverage (fun z ↦ poissonKernel 0 w z ^ 2) 0 1 =
      (1 + Complex.normSq w) / (1 - Complex.normSq w) := by
  let f : ℂ → ℂ := fun z ↦ (1 + star w * z) / (1 - star w * z)
  have hn (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : 1 - star w * z ≠ 0 := by
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    intro h
    have hh : star w * z = 1 := (sub_eq_zero.mp h).symm
    have hnorm := congrArg norm hh
    simp only [norm_mul, norm_star, norm_one] at hnorm
    nlinarith [norm_nonneg w]
  have hh : InnerProductSpace.HarmonicOnNhd (fun z ↦ (f z).re)
      (closedBall (0 : ℂ) 1) := by
    intro z hz
    have : AnalyticAt ℂ f z := by
      unfold f
      fun_prop (disch := exact hn z hz)
    exact this.harmonicAt_re
  have hp := hh.circleAverage_poissonKernel_smul (w := w) (by simpa using hw)
  have he : circleAverage (fun z ↦ poissonKernel 0 w z ^ 2) 0 1 =
      circleAverage (poissonKernel 0 w • (fun z ↦ (f z).re)) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have hz' : ‖z‖ = 1 := by simpa using hz
    change poissonKernel 0 w z ^ 2 = poissonKernel 0 w z * (f z).re
    rw [poissonKernel_zero_eq_analytic w z hz']
    exact pow_two _
  rw [he, hp]
  change ((1 + star w * w) / (1 - star w * w)).re = _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  norm_cast

theorem circleAverage_inv_affine (a : ℝ) (b : ℂ) (ha : ‖b‖ < a) :
    circleAverage (fun z ↦ (a - (b * z).re)⁻¹) 0 1 =
      (Real.sqrt (a ^ 2 - Complex.normSq b))⁻¹ ∧
    circleAverage (fun z ↦ (a - (b * z).re)⁻¹ ^ 2) 0 1 =
      a / (Real.sqrt (a ^ 2 - Complex.normSq b)) ^ 3 := by
  have ha0 : 0 < a := lt_of_le_of_lt (norm_nonneg b) ha
  have hdisc : 0 < a ^ 2 - Complex.normSq b := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg b]
  let r := Real.sqrt (a ^ 2 - Complex.normSq b)
  have hr : 0 < r := Real.sqrt_pos.2 hdisc
  have hr2 : r ^ 2 = a ^ 2 - Complex.normSq b := Real.sq_sqrt hdisc.le
  have hc : 0 < a + r := add_pos ha0 hr
  let w : ℂ := star b / (a + r : ℝ)
  have hw : ‖w‖ < 1 := by
    dsimp [w]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
      div_lt_one hc]
    linarith
  have hw2 : Complex.normSq w = Complex.normSq b / (a + r) ^ 2 := by
    simp only [w, Complex.normSq_div, Complex.star_def, Complex.normSq_conj,
      Complex.normSq_ofReal, pow_two]
  have hcross (z : ℂ) : (star w * z).re = (b * z).re / (a + r) := by
    dsimp only [w]
    rw [star_div₀, star_star]
    rw [show star ((a + r : ℝ) : ℂ) = ((a + r : ℝ) : ℂ) by simp]
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
  have hminus : 1 - Complex.normSq b / (a + r) ^ 2 = 2 * r / (a + r) := by
    field_simp
    nlinarith [hr2]
  have hplus : 1 + Complex.normSq b / (a + r) ^ 2 = 2 * a / (a + r) := by
    field_simp
    nlinarith [hr2]
  have he (z : ℂ) (hz : ‖z‖ = 1) :
      (a - (b * z).re)⁻¹ = r⁻¹ * poissonKernel 0 w z := by
    have hz2 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    have hden : 0 < a - (b * z).re := by
      have h := Complex.re_le_norm (b * z)
      rw [norm_mul, hz, mul_one] at h
      linarith
    rw [poissonKernel_zero_eq _ _ hz, normSq_sub_circle w z hz2, hw2, hcross]
    rw [hminus, hplus]
    field_simp [hc.ne', hr.ne', hden.ne']
  have h1 : circleAverage (fun z ↦ (a - (b * z).re)⁻¹) 0 1 = r⁻¹ := by
    calc
      _ = circleAverage (fun z ↦ r⁻¹ • poissonKernel 0 w z) 0 1 := by
        apply circleAverage_congr_sphere
        intro z hz
        exact he z (by simpa using hz)
      _ = _ := by rw [circleAverage_fun_smul, circleAverage_poisson_zero w hw]; simp
  refine ⟨h1, ?_⟩
  calc
    _ = circleAverage (fun z ↦ r⁻¹ ^ 2 • poissonKernel 0 w z ^ 2) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      dsimp
      rw [he z (by simpa using hz), mul_pow]
    _ = r⁻¹ ^ 2 * ((1 + Complex.normSq w) / (1 - Complex.normSq w)) := by
      rw [circleAverage_fun_smul, circleAverage_poisson_zero_sq w hw, smul_eq_mul]
    _ = _ := by
      rw [hw2]
      change _ = a / r ^ 3
      rw [hminus, hplus]
      field_simp

end NLA.FR05

end
end

/-! ## ConePhaseMeasure -/

section

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real

namespace NLA.FR05

instance conePhasePeriod_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev ConePhase := AddCircle (2 * Real.pi)

def conePhasePoint (θ : ConePhase) : ℂ := AddCircle.toCircle θ

@[fun_prop]
theorem continuous_conePhasePoint : Continuous conePhasePoint :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

@[simp]
theorem norm_conePhasePoint (θ : ConePhase) : ‖conePhasePoint θ‖ = 1 :=
  Circle.norm_coe _

theorem integral_conePhasePoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) :
    (∫ θ : ConePhase, f (conePhasePoint θ) ∂AddCircle.haarAddCircle) =
      circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle, Real.circleAverage,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp [conePhasePoint, AddCircle.toCircle, circleMap]

theorem integral_conePhasePoint_re_mul (b : ℂ) :
    (∫ θ : ConePhase, (b * conePhasePoint θ).re ∂AddCircle.haarAddCircle) = 0 := by
  rw [integral_conePhasePoint (fun z ↦ (b * z).re)]
  have hh : InnerProductSpace.HarmonicOnNhd (fun z : ℂ ↦ (b * z).re)
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) := by
    intro z _
    exact AnalyticAt.harmonicAt_re (by fun_prop)
  simpa using hh.circleAverage_eq

end NLA.FR05

end

end
