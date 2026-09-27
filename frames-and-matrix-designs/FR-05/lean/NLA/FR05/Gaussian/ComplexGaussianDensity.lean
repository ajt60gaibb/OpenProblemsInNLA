import NLA.FR05.Cone.ConeGaussianMoments

/-!
# Complex Gaussian densities and affine transformations

The sections develop `ComplexGaussianDensity`, `ComplexGaussianAffine`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ComplexGaussianDensity

open MeasureTheory ProbabilityTheory Complex Real
open scoped ENNReal NNReal

theorem integral_scalarComplexGaussian_continuous (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ z, f z ∂scalarComplexGaussian) =
      Real.pi⁻¹ * ∫ z : ℂ, Real.exp (-Complex.normSq z) * f z := by
  unfold scalarComplexGaussian
  rw [integral_map continuous_scalarComplexMap.measurable.aemeasurable hf.aestronglyMeasurable,
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.mul_lt_top
        (by simp [gaussianPDF]) (by simp [gaussianPDF]))]
  simp only [ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul, gaussian_real_pair_pdf]
  simp_rw [mul_assoc]
  rw [integral_const_mul, ← Measure.volume_eq_prod,
    ← Complex.volume_preserving_equiv_real_prod.integral_comp']
  have he (z : ℂ) :
      Real.exp (-((z.re ^ 2 + z.im ^ 2) / 2)) * f (scalarComplexMap (z.re, z.im)) =
        (fun w : ℂ ↦ Real.exp (-Complex.normSq w) * f w) ((Real.sqrt 2)⁻¹ • z) := by
    have hm : scalarComplexMap (z.re, z.im) = (Real.sqrt 2)⁻¹ • z := by
      apply Complex.ext <;> simp [scalarComplexMap, Complex.real_smul, div_eq_mul_inv, mul_comm]
    rw [hm]
    congr 2
    simp only [Complex.normSq_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith
  simp only [Complex.measurableEquivRealProd_apply]
  simp_rw [he]
  rw [Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ ↦ Real.exp (-Complex.normSq w) * f w) ((Real.sqrt 2)⁻¹)
    (hR := inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simp only [Complex.finrank_real_complex, smul_eq_mul, inv_pow, inv_inv]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

def scalarComplexDensity (z : ℂ) : ℝ :=
  Real.pi⁻¹ * Real.exp (-Complex.normSq z)

theorem scalarComplexGaussian_eq_withDensity :
    scalarComplexGaussian = volume.withDensity (fun z ↦ ENNReal.ofReal (scalarComplexDensity z)) := by
  have hnon (z : ℂ) : 0 ≤ scalarComplexDensity z := by unfold scalarComplexDensity; positivity
  have hmass : (∫ z : ℂ, scalarComplexDensity z) = 1 := by
    have h := integral_scalarComplexGaussian_continuous (fun _ ↦ 1) continuous_const
    simp only [integral_const, probReal_univ, one_smul, mul_one] at h
    unfold scalarComplexDensity
    rw [integral_const_mul]
    exact h.symm
  have hi : Integrable scalarComplexDensity (volume : Measure ℂ) := by
    by_contra h
    rw [integral_undef h] at hmass
    norm_num at hmass
  have hm : (volume.withDensity (fun z ↦ ENNReal.ofReal (scalarComplexDensity z))) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnon), hmass]
    simp
  let : IsProbabilityMeasure (volume.withDensity (fun z ↦ ENNReal.ofReal (scalarComplexDensity z))) :=
    ⟨hm⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_scalarComplexGaussian_continuous f f.continuous,
    integral_withDensity_eq_integral_toReal_smul (by unfold scalarComplexDensity; fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  have hr (z : ℂ) : (ENNReal.ofReal (scalarComplexDensity z)).toReal = scalarComplexDensity z :=
    ENNReal.toReal_ofReal (hnon z)
  simp_rw [hr]
  unfold scalarComplexDensity
  simp_rw [mul_assoc]
  rw [integral_const_mul]

end ComplexGaussianDensity

section ComplexGaussianAffine

open MeasureTheory ProbabilityTheory Complex Real
open scoped ENNReal

theorem scalarComplexDensity_nonneg (z : ℂ) : 0 ≤ scalarComplexDensity z := by
  unfold scalarComplexDensity
  positivity

theorem integral_scalarComplexGaussian (f : ℂ → ℝ) :
    (∫ z, f z ∂scalarComplexGaussian) = ∫ z : ℂ, scalarComplexDensity z * f z := by
  rw [scalarComplexGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (by unfold scalarComplexDensity; fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have he (z : ℂ) : (ENNReal.ofReal (scalarComplexDensity z)).toReal = scalarComplexDensity z :=
    ENNReal.toReal_ofReal (scalarComplexDensity_nonneg z)
  simp_rw [he]
  rfl

def scalarGaussianDensity (a : ℝ) (m z : ℂ) : ℝ :=
  (Real.pi * a)⁻¹ * Real.exp (-Complex.normSq (z - m) / a)

theorem scalarGaussianDensity_affine {a : ℝ} (ha : 0 < a) (m z : ℂ) :
    a * scalarGaussianDensity a m (Real.sqrt a • z + m) = scalarComplexDensity z := by
  have hnorm : Complex.normSq (Real.sqrt a • z) = a * Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ha.le,
      ← Complex.normSq_eq_norm_sq]
  unfold scalarGaussianDensity scalarComplexDensity
  rw [add_sub_cancel_right, hnorm]
  have he : -(a * Complex.normSq z) / a = -Complex.normSq z := by field_simp
  rw [he]
  field_simp

theorem integral_scalarGaussianDensity {a : ℝ} (ha : 0 < a) (m : ℂ) (f : ℂ → ℝ) :
    (∫ z : ℂ, scalarGaussianDensity a m z * f z) =
      ∫ z, f (Real.sqrt a • z + m) ∂scalarComplexGaussian := by
  rw [integral_scalarComplexGaussian]
  have he (z : ℂ) : scalarComplexDensity z * f (Real.sqrt a • z + m) =
      a * (scalarGaussianDensity a m (Real.sqrt a • z + m) * f (Real.sqrt a • z + m)) := by
    rw [← scalarGaussianDensity_affine ha m z]
    ring
  simp_rw [he]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
      (fun z ↦ scalarGaussianDensity a m (z + m) * f (z + m)) (Real.sqrt a)
      (hR := Real.sqrt_nonneg a)]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [Real.sq_sqrt ha.le, integral_add_right_eq_self (fun z : ℂ ↦ scalarGaussianDensity a m z * f z) m]
  field_simp

theorem integrable_scalarGaussianDensity {a : ℝ} (ha : 0 < a) (m : ℂ) :
    Integrable (scalarGaussianDensity a m) (volume : Measure ℂ) := by
  have h := integral_scalarGaussianDensity ha m (fun _ ↦ 1)
  simp only [mul_one, integral_const, probReal_univ, one_smul] at h
  by_contra hi
  rw [integral_undef hi] at h
  norm_num at h

theorem scalarGaussianDensity_integral {a : ℝ} (ha : 0 < a) (m : ℂ) :
    (∫ z : ℂ, scalarGaussianDensity a m z) = 1 := by
  simpa using integral_scalarGaussianDensity ha m (fun _ ↦ 1)

end ComplexGaussianAffine

end NLA.FR05
