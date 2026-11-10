import NLA.Proofs.IE22.GaussianCovariance
import NLA.Proofs.IE22.GaussianBasics

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

/-- The literal real interval integral is the actual truncated Gaussian second moment. -/
theorem gaussian_truncated_second_moment {a : ℝ} (ha : 0 ≤ a) :
    (∫ z in Set.Icc (-a) a, z^2 ∂gaussianReal 0 1) = TrimmedMoment a := by
  have hden : (∫ z in Set.Icc (-a) a, z^2 ∂gaussianReal 0 1) =
      ∫ z in Set.Icc (-a) a, gaussianPDFReal 0 1 z * z^2 := by
    calc
      _ = ∫ z, (Set.Icc (-a) a).indicator (fun z : ℝ => z^2) z ∂gaussianReal 0 1 :=
        (integral_indicator measurableSet_Icc).symm
      _ = ∫ z, gaussianPDFReal 0 1 z *
          (Set.Icc (-a) a).indicator (fun z : ℝ => z^2) z := by
        exact integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)
      _ = ∫ z, (Set.Icc (-a) a).indicator
          (fun z : ℝ => gaussianPDFReal 0 1 z * z^2) z := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          by_cases hz : z ∈ Set.Icc (-a) a <;> simp [hz]
      _ = _ := integral_indicator measurableSet_Icc
  rw [hden]
  unfold TrimmedMoment
  have hfun : (fun z : ℝ => gaussianPDFReal 0 1 z * z^2) =
      fun z => (1 / Real.sqrt (2*Real.pi)) * (z^2 * Real.exp (-(z^2)/2)) := by
    ext z
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    ring
  rw [hfun, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]

/-- The actual truncated moment is nonnegative. -/
theorem trimmedMoment_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ TrimmedMoment a := by
  rw [← gaussian_truncated_second_moment ha]
  exact integral_nonneg fun z => sq_nonneg z

/-- The actual truncated moment is at most the full unit Gaussian variance. -/
theorem trimmedMoment_le_one {a : ℝ} (ha : 0 ≤ a) : TrimmedMoment a ≤ 1 := by
  rw [← gaussian_truncated_second_moment ha, ← normal_second_moment]
  apply integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun z => sq_nonneg z) normal_square_integrable

/-- Integrating the fixed quantile selector gives its exact finite second moment. -/
theorem gaussian_quantile_selector_integral {θ a : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hquantile : GaussianQuantile θ a) (t : ℝ) :
    (∫ z in Set.Icc (-a) a, (t-z^2) ∂gaussianReal 0 1) = θ*t - TrimmedMoment a := by
  rw [integral_sub (integrable_const t) normal_square_integrable.restrict,
    gaussian_truncated_second_moment ha]
  have hmass : (gaussianReal 0 1).real (Set.Icc (-a) a) = θ := by
    change ((gaussianReal 0 1) (Set.Icc (-a) a)).toReal = θ
    change (gaussianReal 0 1) (Set.Icc (-a) a) = ENNReal.ofReal θ at hquantile
    rw [hquantile, ENNReal.toReal_ofReal hθ]
  simp [hmass, mul_comm]

/-- Every nonnegative trimming threshold is bounded by the literal quantile moment. -/
theorem gaussian_hinge_dual_le {θ a : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hquantile : GaussianQuantile θ a) {t : ℝ} (ht : 0 ≤ t) :
    θ*t - (∫ z : ℝ, hinge t z ∂gaussianReal 0 1) ≤ TrimmedMoment a := by
  have hhinge : Integrable (hinge t) (gaussianReal 0 1) :=
    (memLp_comp_lipschitz (memLp_id_gaussianReal' 2 (by norm_num))
      (hinge_lipschitz ht)).integrable (by norm_num)
  have hle : (∫ z in Set.Icc (-a) a, (t-z^2) ∂gaussianReal 0 1) ≤
      ∫ z : ℝ, hinge t z ∂gaussianReal 0 1 := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_mono
      (((integrable_const t).sub normal_square_integrable).indicator measurableSet_Icc)
      hhinge
    intro z
    by_cases hz : z ∈ Set.Icc (-a) a
    · simpa [hz, hinge] using (le_max_left (t-z^2) 0)
    · simpa [hz] using hinge_nonneg t z
  rw [gaussian_quantile_selector_integral hθ ha hquantile] at hle
  linarith

/-- The exact Gaussian quantile threshold attains the population trimming dual. -/
theorem gaussian_hinge_quantile_eq {θ a : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hquantile : GaussianQuantile θ a) :
    (∫ z : ℝ, hinge (a^2) z ∂gaussianReal 0 1) = θ*a^2 - TrimmedMoment a := by
  have heq : hinge (a^2) = (Set.Icc (-a) a).indicator (fun z : ℝ => a^2-z^2) := by
    ext z
    by_cases hz : z ∈ Set.Icc (-a) a
    · have habs : |z| ≤ a := abs_le.mpr hz
      have hs := (sq_le_sq₀ (abs_nonneg z) ha).2 habs
      have hzsq : z^2 ≤ a^2 := by simpa only [sq_abs] using hs
      simp [hz, hinge, max_eq_left (sub_nonneg.mpr hzsq)]
    · have habs : a < |z| := lt_of_not_ge (by intro hzabs; exact hz (abs_le.mp hzabs))
      have hs : a^2 ≤ z^2 := by nlinarith [abs_nonneg z, sq_abs z]
      simp [hz, hinge, max_eq_right (sub_nonpos.mpr hs)]
  rw [heq, integral_indicator measurableSet_Icc]
  exact gaussian_quantile_selector_integral hθ ha hquantile _

#assert_trust kernel gaussian_truncated_second_moment
#assert_trust kernel trimmedMoment_nonneg
#assert_trust kernel trimmedMoment_le_one
#assert_trust kernel gaussian_quantile_selector_integral
#assert_trust kernel gaussian_hinge_dual_le
#assert_trust kernel gaussian_hinge_quantile_eq
#print axioms gaussian_hinge_quantile_eq
end NLA.Proofs.IE22
