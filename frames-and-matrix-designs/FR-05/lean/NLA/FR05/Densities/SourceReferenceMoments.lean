import NLA.FR05.Gaussian.RadialMoments
import NLA.FR05.Densities.SourceLikelihood

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.FR05

theorem sourceRadiusSq_eq_signalEnergy (z : Fin 2 → ℂ) :
    sourceRadiusSq z = signalEnergy z := by
  simp [sourceRadiusSq, signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two]

theorem sourceReferenceDensity_mul_exp (M : ℕ) (t : ℝ) (z : Fin 2 → ℂ) :
    sourceReferenceDensity M z * Real.exp (t * sourceRadiusSq z) =
      (sourceVariance M)⁻¹ ^ 2 *
        Real.exp ((t + 1 - (sourceVariance M)⁻¹) * signalEnergy z) := by
  unfold sourceReferenceDensity
  rw [sourceRadiusSq_eq_signalEnergy, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrable_sourceReferenceDensity_mul_exp (M : ℕ) {t : ℝ}
    (ht : t < (sourceVariance M)⁻¹) :
    Integrable (fun z ↦ sourceReferenceDensity M z * Real.exp (t * sourceRadiusSq z))
      (standardComplexGaussianTail 2) := by
  simp_rw [sourceReferenceDensity_mul_exp]
  exact (integrable_exp_standardComplexGaussian_energy 2 (by linarith)).const_mul _

/-- The exact radial exponential moment of the reference density (3.4). -/
theorem integral_sourceReferenceDensity_mul_exp (M : ℕ) {t : ℝ}
    (ht : t < (sourceVariance M)⁻¹) :
    (∫ z, sourceReferenceDensity M z * Real.exp (t * sourceRadiusSq z)
      ∂standardComplexGaussianTail 2) = (1 - sourceVariance M * t)⁻¹ ^ 2 := by
  simp_rw [sourceReferenceDensity_mul_exp]
  rw [integral_const_mul]
  change (sourceVariance M)⁻¹ ^ 2 *
    mgf (signalEnergy (n := 2)) (standardComplexGaussianTail 2)
      (t + 1 - (sourceVariance M)⁻¹) = _
  rw [mgf_standardComplexGaussian_energy 2 (by linarith)]
  have hv := (sourceVariance_pos M).ne'
  have ht' : 1 - sourceVariance M * t ≠ 0 := by
    have hmul := mul_lt_mul_of_pos_left ht (sourceVariance_pos M)
    rw [mul_inv_cancel₀ hv] at hmul
    linarith
  have he : 1 - (t + 1 - (sourceVariance M)⁻¹) =
      (1 - sourceVariance M * t) / sourceVariance M := by
    field_simp
    ring
  rw [he, inv_div, div_pow]
  field_simp

theorem integrable_sourceReferenceDensity (M : ℕ) :
    Integrable (sourceReferenceDensity M) (standardComplexGaussianTail 2) := by
  simpa using integrable_sourceReferenceDensity_mul_exp M
    (t := 0) (inv_pos.mpr (sourceVariance_pos M))

theorem integral_sourceReferenceDensity (M : ℕ) :
    (∫ z, sourceReferenceDensity M z ∂standardComplexGaussianTail 2) = 1 := by
  simpa using integral_sourceReferenceDensity_mul_exp M
    (t := 0) (inv_pos.mpr (sourceVariance_pos M))

private theorem sourceReferenceDensity_mul_radius_pow (M k : ℕ) (z : Fin 2 → ℂ) :
    sourceReferenceDensity M z * sourceRadiusSq z ^ k =
      (sourceVariance M)⁻¹ ^ 2 *
        (signalEnergy z ^ k * Real.exp ((1 - (sourceVariance M)⁻¹) * signalEnergy z)) := by
  unfold sourceReferenceDensity
  rw [sourceRadiusSq_eq_signalEnergy]
  have he : -((sourceVariance M)⁻¹ - 1) = 1 - (sourceVariance M)⁻¹ := by ring
  rw [he]
  ring

theorem integrable_sourceReferenceDensity_mul_radius_pow (M k : ℕ) :
    Integrable (fun z ↦ sourceReferenceDensity M z * sourceRadiusSq z ^ k)
      (standardComplexGaussianTail 2) := by
  simp_rw [sourceReferenceDensity_mul_radius_pow]
  apply Integrable.const_mul
  apply integrable_energy_pow_mul_exp_standardComplexGaussian
  have := inv_pos.mpr (sourceVariance_pos M)
  linarith

theorem integral_sourceReferenceDensity_mul_radius (M : ℕ) :
    (∫ z, sourceReferenceDensity M z * sourceRadiusSq z
      ∂standardComplexGaussianTail 2) = 2 * sourceVariance M := by
  have he (z : Fin 2 → ℂ) := sourceReferenceDensity_mul_radius_pow M 1 z
  simp only [pow_one] at he
  simp_rw [he]
  rw [integral_const_mul, integral_energy_mul_exp_standardComplexGaussian_two (by
    have := inv_pos.mpr (sourceVariance_pos M)
    linarith)]
  simp only [sub_sub_cancel, inv_inv]
  field_simp [(sourceVariance_pos M).ne']

theorem integral_sourceReferenceDensity_mul_radius_sq (M : ℕ) :
    (∫ z, sourceReferenceDensity M z * sourceRadiusSq z ^ 2
      ∂standardComplexGaussianTail 2) = 6 * sourceVariance M ^ 2 := by
  simp_rw [sourceReferenceDensity_mul_radius_pow]
  rw [integral_const_mul, integral_energy_sq_mul_exp_standardComplexGaussian_two (by
    have := inv_pos.mpr (sourceVariance_pos M)
    linarith)]
  simp only [sub_sub_cancel, inv_inv]
  field_simp [(sourceVariance_pos M).ne']

/-- The reference exponential moment is uniformly bounded at the source's scale. -/
theorem sourceReferenceDensity_exp_quarter_bound {M : ℕ} (hM : 2 ≤ M) :
    (∫ z, sourceReferenceDensity M z * Real.exp (sourceRadiusSq z / 4)
      ∂standardComplexGaussianTail 2) ≤ 16 / 9 := by
  have hv := sourceVariance_pos M
  have hv' := sourceVariance_le_one hM
  have hi : (1 / 4 : ℝ) < (sourceVariance M)⁻¹ := by
    have : 1 ≤ (sourceVariance M)⁻¹ := (one_le_inv₀ hv).mpr hv'
    linarith
  have he : (fun z ↦ sourceReferenceDensity M z * Real.exp (sourceRadiusSq z / 4)) =
      fun z ↦ sourceReferenceDensity M z * Real.exp ((1 / 4) * sourceRadiusSq z) := by
    funext z
    congr 2
    ring
  rw [he, integral_sourceReferenceDensity_mul_exp M hi]
  have hden : 0 < 1 - sourceVariance M * (1 / 4) := by linarith
  have hle : (1 - sourceVariance M * (1 / 4))⁻¹ ≤ 4 / 3 := by
    apply (inv_le_iff_one_le_mul₀ hden).mpr
    linarith
  nlinarith [inv_nonneg.mpr hden.le]

/-- The probability law with the actual reference density relative to γ₂. -/
def sourceReferenceLaw (M : ℕ) : Measure (Fin 2 → ℂ) :=
  (standardComplexGaussianTail 2).withDensity (fun z ↦ ENNReal.ofReal (sourceReferenceDensity M z))

instance isProbabilityMeasure_sourceReferenceLaw (M : ℕ) :
    IsProbabilityMeasure (sourceReferenceLaw M) where
  measure_univ := by
    rw [sourceReferenceLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_sourceReferenceDensity M)
        (Filter.Eventually.of_forall fun z ↦ (sourceReferenceDensity_pos M z).le),
      integral_sourceReferenceDensity]
    norm_num

theorem integral_sourceReferenceLaw (M : ℕ) (f : (Fin 2 → ℂ) → ℝ) :
    (∫ z, f z ∂sourceReferenceLaw M) =
      ∫ z, sourceReferenceDensity M z * f z ∂standardComplexGaussianTail 2 := by
  rw [sourceReferenceLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_sourceReferenceDensity M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceReferenceDensity_pos M _).le, smul_eq_mul]

theorem integrable_sourceReferenceLaw_iff (M : ℕ) (f : (Fin 2 → ℂ) → ℝ) :
    Integrable f (sourceReferenceLaw M) ↔
      Integrable (fun z ↦ sourceReferenceDensity M z * f z)
        (standardComplexGaussianTail 2) := by
  rw [sourceReferenceLaw, integrable_withDensity_iff_integrable_smul'
    (measurable_sourceReferenceDensity M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceReferenceDensity_pos M _).le, smul_eq_mul]

theorem integrable_exp_sourceReferenceLaw (M : ℕ) {t : ℝ}
    (ht : t < (sourceVariance M)⁻¹) :
    Integrable (fun z ↦ Real.exp (t * sourceRadiusSq z)) (sourceReferenceLaw M) :=
  (integrable_sourceReferenceLaw_iff M _).mpr
    (integrable_sourceReferenceDensity_mul_exp M ht)

theorem mgf_sourceReferenceLaw (M : ℕ) {t : ℝ} (ht : t < (sourceVariance M)⁻¹) :
    mgf sourceRadiusSq (sourceReferenceLaw M) t = (1 - sourceVariance M * t)⁻¹ ^ 2 := by
  rw [mgf, integral_sourceReferenceLaw]
  exact integral_sourceReferenceDensity_mul_exp M ht

theorem integrable_radius_pow_sourceReferenceLaw (M k : ℕ) :
    Integrable (fun z ↦ sourceRadiusSq z ^ k) (sourceReferenceLaw M) :=
  (integrable_sourceReferenceLaw_iff M _).mpr
    (integrable_sourceReferenceDensity_mul_radius_pow M k)

theorem integral_radius_sourceReferenceLaw (M : ℕ) :
    (∫ z, sourceRadiusSq z ∂sourceReferenceLaw M) = 2 * sourceVariance M := by
  rw [integral_sourceReferenceLaw, integral_sourceReferenceDensity_mul_radius]

theorem integral_radius_sq_sourceReferenceLaw (M : ℕ) :
    (∫ z, sourceRadiusSq z ^ 2 ∂sourceReferenceLaw M) = 6 * sourceVariance M ^ 2 := by
  rw [integral_sourceReferenceLaw, integral_sourceReferenceDensity_mul_radius_sq]

theorem sourceReferenceLaw_exp_quarter_bound {M : ℕ} (hM : 2 ≤ M) :
    (∫ z, Real.exp (sourceRadiusSq z / 4) ∂sourceReferenceLaw M) ≤ 16 / 9 := by
  rw [integral_sourceReferenceLaw]
  exact sourceReferenceDensity_exp_quarter_bound hM

end NLA.FR05
