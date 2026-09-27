import NLA.FR05.Cone.ConeRayDensity

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real Matrix
open scoped ENNReal

namespace NLA.FR05

@[fun_prop] theorem continuous_coneRadialWeight : Continuous coneRadialWeight := by
  unfold coneRadialWeight
  fun_prop

def coneScalarMeasure : Measure ℂ :=
  scalarComplexGaussian.withDensity (fun z ↦ ENNReal.ofReal (coneRadialWeight z))


theorem coneScalarMeasure_eq_density :
    coneScalarMeasure = (volume : Measure ℂ).withDensity
      (fun z ↦ ENNReal.ofReal (scalarComplexDensity z * coneRadialWeight z)) := by
  rw [coneScalarMeasure, scalarComplexGaussian_eq_withDensity,
    ← withDensity_mul _ (by unfold scalarComplexDensity; fun_prop) (by fun_prop)]
  congr 1
  funext z
  exact (ENNReal.ofReal_mul (scalarComplexDensity_nonneg z)).symm

theorem integrable_coneRadialWeight : Integrable coneRadialWeight scalarComplexGaussian := by
  have hn : Integrable (fun z ↦ Complex.normSq z) scalarComplexGaussian := by
    simpa using integrable_scalarGaussian_normSq_pow 1
  exact (integrable_const _).add (hn.const_mul _)

theorem integral_coneRadialWeight : (∫ z, coneRadialWeight z ∂scalarComplexGaussian) = 1 := by
  unfold coneRadialWeight
  have hn : Integrable (fun z ↦ Complex.normSq z) scalarComplexGaussian := by
    simpa using integrable_scalarGaussian_normSq_pow 1
  rw [integral_add (integrable_const _) (hn.const_mul _)]
  simp [integral_const_mul, integral_scalarGaussian_normSq]

instance isProbabilityMeasure_coneScalarMeasure : IsProbabilityMeasure coneScalarMeasure := by
  constructor
  rw [coneScalarMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_coneRadialWeight
      (Filter.Eventually.of_forall fun z ↦ (coneRadialWeight_pos z).le),
    integral_coneRadialWeight]
  norm_num

def conePoint (t : ℝ) (p : ConePhase × ℂ) : Fin 2 → ℂ :=
  coneBasis t (conePhasePoint p.1) *ᵥ ![p.2, 0]

@[fun_prop] theorem continuous_conePoint (t : ℝ) : Continuous (conePoint t) := by
  unfold conePoint coneBasis
  fun_prop

theorem conePoint_eq (t : ℝ) (p : ConePhase × ℂ) :
    conePoint t p = fun i ↦ coneDirection t (conePhasePoint p.1) i * p.2 := by
  ext i
  fin_cases i <;> simp [conePoint, coneBasis, coneDirection, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

def coneMeasure (t : ℝ) : Measure (Fin 2 → ℂ) :=
  (AddCircle.haarAddCircle.prod coneScalarMeasure).map (conePoint t)

instance isProbabilityMeasure_coneMeasure (t : ℝ) : IsProbabilityMeasure (coneMeasure t) :=
  Measure.isProbabilityMeasure_map (continuous_conePoint t).measurable.aemeasurable

@[fun_prop] theorem continuous_overlapGaussianRatio (K : SourceOverlapMatrix) :
    Continuous (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦ overlapGaussianRatio K p.1 p.2) := by
  unfold overlapGaussianRatio coneInner sourceRadiusSq
  fun_prop

def coneCorrelation (K : SourceOverlapMatrix) (t s : ℝ) : ℝ :=
  ∫ p, overlapGaussianRatio K p.1 p.2 ∂(coneMeasure t).prod (coneMeasure s)

theorem lintegral_coneMeasure (t : ℝ) (f : (Fin 2 → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂coneMeasure t) =
      ∫⁻ φ, ∫⁻ x, ENNReal.ofReal (coneRadialWeight x) * f (conePoint t (φ, x))
        ∂scalarComplexGaussian ∂AddCircle.haarAddCircle := by
  rw [coneMeasure, lintegral_map hf (continuous_conePoint t).measurable,
    lintegral_prod (fun p : ConePhase × ℂ ↦ f (conePoint t p))
      (by exact (hf.comp (continuous_conePoint t).measurable).aemeasurable)]
  apply lintegral_congr
  intro φ
  rw [coneScalarMeasure, lintegral_withDensity_eq_lintegral_mul scalarComplexGaussian
    (g := fun y : ℂ ↦ f (conePoint t (φ, y)))
    (by unfold coneRadialWeight; fun_prop) (by fun_prop)]
  rfl

theorem lintegral_coneCorrelation {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    (∫⁻ p, ENNReal.ofReal (overlapGaussianRatio K p.1 p.2)
      ∂(coneMeasure t).prod (coneMeasure s)) =
      ∫⁻ p, ENNReal.ofReal (coneRayMoment (coneRotatedOverlap K t s p.1 p.2))
        ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
  have hR : Measurable (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
      ENNReal.ofReal (overlapGaussianRatio K p.1 p.2)) := by fun_prop
  rw [lintegral_prod _ hR.aemeasurable, lintegral_coneMeasure t _ (by fun_prop)]
  have hinner (z : Fin 2 → ℂ) :
      (∫⁻ w, ENNReal.ofReal (overlapGaussianRatio K z w) ∂coneMeasure s) =
      ∫⁻ ψ, ∫⁻ y, ENNReal.ofReal (coneRadialWeight y) *
        ENNReal.ofReal (overlapGaussianRatio K z (conePoint s (ψ, y)))
        ∂scalarComplexGaussian ∂AddCircle.haarAddCircle :=
    lintegral_coneMeasure s _ (by fun_prop)
  simp_rw [hinner]
  have hmove (φ : ConePhase) (x : ℂ) :
      ENNReal.ofReal (coneRadialWeight x) *
        (∫⁻ ψ, ∫⁻ y, ENNReal.ofReal (coneRadialWeight y) *
          ENNReal.ofReal (overlapGaussianRatio K (conePoint t (φ, x)) (conePoint s (ψ, y)))
          ∂scalarComplexGaussian ∂AddCircle.haarAddCircle) =
      ∫⁻ ψ, ∫⁻ y, ENNReal.ofReal
        (coneRadialWeight x * coneRadialWeight y *
          overlapGaussianRatio K (conePoint t (φ, x)) (conePoint s (ψ, y)))
        ∂scalarComplexGaussian ∂AddCircle.haarAddCircle := by
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr
    intro ψ
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (mul_nonneg (coneRadialWeight_pos x).le (coneRadialWeight_pos y).le),
      ENNReal.ofReal_mul (coneRadialWeight_pos x).le, mul_assoc]
  simp_rw [hmove]
  have hswap (φ : ConePhase) :
      (∫⁻ x, ∫⁻ ψ, ∫⁻ y, ENNReal.ofReal
        (coneRadialWeight x * coneRadialWeight y *
          overlapGaussianRatio K (conePoint t (φ, x)) (conePoint s (ψ, y)))
        ∂scalarComplexGaussian ∂AddCircle.haarAddCircle ∂scalarComplexGaussian) =
      ∫⁻ ψ, ∫⁻ x, ∫⁻ y, ENNReal.ofReal
        (coneRadialWeight x * coneRadialWeight y *
          overlapGaussianRatio K (conePoint t (φ, x)) (conePoint s (ψ, y)))
        ∂scalarComplexGaussian ∂scalarComplexGaussian ∂AddCircle.haarAddCircle := by
    apply lintegral_lintegral_swap
    apply Measurable.aemeasurable
    unfold coneRadialWeight
    fun_prop
  simp_rw [hswap]
  rw [lintegral_prod _ (by
    apply Measurable.aemeasurable
    exact (continuous_coneRayMoment_pair hK ht hs).measurable.ennreal_ofReal)]
  apply lintegral_congr
  intro φ
  apply lintegral_congr
  intro ψ
  have hL : overlapOperatorNorm (coneRotatedOverlap K t s φ ψ) < 1 :=
    lt_of_le_of_lt (coneRotatedOverlap_norm_le ht hs K φ ψ) hK
  simp only [conePoint, overlapGaussianRatio_coneBasis ht hs]
  rw [← lintegral_prod (fun p : ℂ × ℂ ↦ ENNReal.ofReal
    (coneRadialWeight p.1 * coneRadialWeight p.2 *
      overlapGaussianRatio (coneRotatedOverlap K t s φ ψ) ![p.1, 0] ![p.2, 0]))
    (by unfold coneRadialWeight overlapGaussianRatio coneInner sourceRadiusSq; fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_cone_ray hL)
      (Filter.Eventually.of_forall fun p ↦
        (mul_pos (mul_pos (coneRadialWeight_pos p.1) (coneRadialWeight_pos p.2))
          (overlapGaussianRatio_pos hL _ _)).le),
    integral_cone_ray_prod hL]

theorem coneCorrelation_eq_moment {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    coneCorrelation K t s = coneMomentCorrelation K t s := by
  have hi := (continuous_coneRayMoment_pair hK ht hs).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hp (p : ConePhase × ConePhase) : 0 ≤ coneRayMoment (coneRotatedOverlap K t s p.1 p.2) :=
    (coneRayMoment_pos
      (lt_of_le_of_lt (coneRotatedOverlap_norm_le ht hs K p.1 p.2) hK)).le
  unfold coneCorrelation
  rw [integral_eq_lintegral_of_nonneg_ae
    (f := fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦ overlapGaussianRatio K p.1 p.2)
    (Filter.Eventually.of_forall fun p ↦ (overlapGaussianRatio_pos hK p.1 p.2).le)
    (continuous_overlapGaussianRatio K).aestronglyMeasurable,
    lintegral_coneCorrelation hK ht hs,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp),
    ENNReal.toReal_ofReal (integral_nonneg hp)]
  rfl

theorem lemma_3_3_sqrt {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    coneCorrelation K t s ≤
      Real.exp (t ^ 2 + s ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
        (Real.sqrt (Real.sqrt (overlapDeterminant K)))⁻¹ := by
  rw [coneCorrelation_eq_moment hK (le_trans ht (by norm_num)) (le_trans hs (by norm_num))]
  exact coneMomentCorrelation_bound hK ht hs

theorem integrable_coneCorrelation {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    Integrable (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦ overlapGaussianRatio K p.1 p.2)
      ((coneMeasure t).prod (coneMeasure s)) := by
  refine ⟨(continuous_overlapGaussianRatio K).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (f := fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦ overlapGaussianRatio K p.1 p.2)
    (Filter.Eventually.of_forall fun p ↦ (overlapGaussianRatio_pos hK p.1 p.2).le),
    lintegral_coneCorrelation hK ht hs]
  have hi := (continuous_coneRayMoment_pair hK ht hs).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun p ↦ (coneRayMoment_pos
      (lt_of_le_of_lt (coneRotatedOverlap_norm_le ht hs K p.1 p.2) hK)).le)]
  exact ENNReal.ofReal_lt_top

theorem lemma_3_3 {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    coneCorrelation K t s ≤
      Real.exp (t ^ 2 + s ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
        overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
  have hpow : (Real.sqrt (Real.sqrt (overlapDeterminant K)))⁻¹ =
      overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (overlapDeterminant_pos hK).le,
      Real.rpow_neg (overlapDeterminant_pos hK).le]
    norm_num
  simpa only [hpow] using lemma_3_3_sqrt hK ht hs


end NLA.FR05
