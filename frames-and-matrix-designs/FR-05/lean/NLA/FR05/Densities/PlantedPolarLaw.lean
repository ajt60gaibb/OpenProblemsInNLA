import NLA.FR05.Cone.ConeMagnitudeCoordinates
import NLA.FR05.Densities.SourceDensityMoments

/-!
# Planted polar and magnitude laws

The sections develop `PlantedPolarLaw`, `PlantedMagnitudeLaw`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section PlantedPolarLaw

open MeasureTheory ProbabilityTheory Complex Real
open scoped ENNReal

def phaseVectorMap (p : (Fin 2 → ℝ) × (Fin 2 → ConePhase)) : Signal 2 :=
  fun i ↦ (Real.sqrt (p.1 i) : ℂ) * conePhasePoint (p.2 i)

@[fun_prop]
theorem continuous_phaseVectorMap : Continuous phaseVectorMap := by
  unfold phaseVectorMap
  fun_prop

def magnitudeGaussianLaw : Measure (Fin 2 → ℝ) := Measure.pi (fun _ ↦ expMeasure 1)
def phaseVectorLaw : Measure (Fin 2 → ConePhase) := Measure.pi (fun _ ↦ AddCircle.haarAddCircle)

instance : IsProbabilityMeasure magnitudeGaussianLaw := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  unfold magnitudeGaussianLaw
  infer_instance

instance : IsProbabilityMeasure phaseVectorLaw := by
  unfold phaseVectorLaw
  infer_instance

theorem standardComplexGaussianTail_two_polar :
    standardComplexGaussianTail 2 = (magnitudeGaussianLaw.prod phaseVectorLaw).map phaseVectorMap := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  let : IsProbabilityMeasure (((expMeasure 1).prod AddCircle.haarAddCircle).map scalarPolarMap) :=
    Measure.isProbabilityMeasure_map continuous_scalarPolarMap.measurable.aemeasurable
  rw [standardComplexGaussianTail_eq_pi]
  simp_rw [scalarComplexGaussian_eq_polar]
  rw [← Measure.pi_map_pi (f := fun _ : Fin 2 ↦ scalarPolarMap)
    (fun _ ↦ continuous_scalarPolarMap.measurable.aemeasurable)]
  have h := (measurePreserving_arrowProdEquivProdArrow ℝ ConePhase (Fin 2)
    (fun _ ↦ expMeasure 1) (fun _ ↦ AddCircle.haarAddCircle)).symm.map_eq
  rw [← h, Measure.map_map (by fun_prop)
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ConePhase (Fin 2)).symm.measurable]
  rfl

theorem ae_magnitudeGaussianLaw_nonneg :
    ∀ᵐ r ∂magnitudeGaussianLaw, ∀ i, 0 ≤ r i := by
  change ∀ᵐ r ∂Measure.pi (fun _ : Fin 2 ↦ expMeasure 1), ∀ i, 0 ≤ r i
  rw [← standardComplexGaussianTail_map_normSq 2]
  apply (ae_map_iff (by apply Measurable.aemeasurable; fun_prop)
    (by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i ↦
        measurableSet_le measurable_const (measurable_pi_apply i))).mpr
  exact Filter.Eventually.of_forall fun z i ↦ Complex.normSq_nonneg (z i)

theorem phaseVectorMap_normSq (r : Fin 2 → ℝ) (θ : Fin 2 → ConePhase)
    (hr : ∀ i, 0 ≤ r i) (i : Fin 2) :
    Complex.normSq (phaseVectorMap (r, θ) i) = r i := by
  simp [phaseVectorMap, Complex.normSq_eq_norm_sq,
    Real.sq_sqrt (hr i)]

def plantedMagnitudeWeight (M : ℕ) (r : Fin 2 → ℝ) : ℝ :=
  magnitudeCone (sourceDelta M) (sourceEpsilon M)
    (fun s ↦ (sourceEta + (1 - sourceEta) / s) /
      (sourceEpsilon M * sourceRadialNormalizer M)) (r 0, r 1)

theorem measurable_plantedMagnitudeWeight (M : ℕ) : Measurable (plantedMagnitudeWeight M) := by
  exact (measurable_magnitudeCone _ _ (by fun_prop)).comp (by fun_prop)

theorem sourcePlantedDensity_phaseVectorMap {M : ℕ} (hM : 1 ≤ M)
    (r : Fin 2 → ℝ) (θ : Fin 2 → ConePhase) (hr : ∀ i, 0 ≤ r i) :
    sourcePlantedDensity M (phaseVectorMap (r, θ)) = plantedMagnitudeWeight M r := by
  have h := sourcePlantedDensity_mul_radial_eq_cone hM (fun _ ↦ 1) (phaseVectorMap (r, θ))
  simpa only [mul_one, phaseVectorMap_normSq r θ hr, plantedMagnitudeWeight] using h

def plantedMagnitudeLaw (M : ℕ) : Measure (Fin 2 → ℝ) :=
  magnitudeGaussianLaw.withDensity (fun r ↦ ENNReal.ofReal (plantedMagnitudeWeight M r))

theorem sourcePlantedDensityLaw_eq_polar {M : ℕ} (hM : 1 ≤ M) :
    sourceDensityLaw .planted M = ((plantedMagnitudeLaw M).prod phaseVectorLaw).map phaseVectorMap := by
  change (standardComplexGaussianTail 2).withDensity
    (fun z ↦ ENNReal.ofReal (sourcePlantedDensity M z)) = _
  rw [standardComplexGaussianTail_two_polar,
    ← map_withDensity_comp _ _ continuous_phaseVectorMap.measurable _
      (measurable_sourcePlantedDensity M).ennreal_ofReal]
  rw [plantedMagnitudeLaw, prod_withDensity_left (measurable_plantedMagnitudeWeight M).ennreal_ofReal]
  congr 1
  apply withDensity_congr_ae
  have hn : ∀ᵐ p ∂magnitudeGaussianLaw.prod phaseVectorLaw, ∀ i, 0 ≤ p.1 i := by
    exact Measure.quasiMeasurePreserving_fst.ae ae_magnitudeGaussianLaw_nonneg
  filter_upwards [hn] with p hp
  rw [sourcePlantedDensity_phaseVectorMap hM p.1 p.2 hp]

end PlantedPolarLaw

section PlantedMagnitudeLaw

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

def magnitudeGaussianDensity (r : Fin 2 → ℝ) : ℝ :=
  gammaPDFReal 1 1 (r 0) * gammaPDFReal 1 1 (r 1)

theorem magnitudeGaussianLaw_eq_density :
    magnitudeGaussianLaw = volume.withDensity (fun r ↦ ENNReal.ofReal (magnitudeGaussianDensity r)) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  let pack : ℝ × ℝ → Fin 2 → ℝ := fun p ↦ ![p.1, p.2]
  have hm : Measurable pack := by dsimp [pack]; fun_prop
  have hExp : ((expMeasure 1).prod (expMeasure 1)).map pack = magnitudeGaussianLaw :=
    (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ expMeasure 1)).symm.map_eq
  have hVol : (volume : Measure (ℝ × ℝ)).map pack = volume := by
    rw [Measure.volume_eq_prod]
    convert! (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ (volume : Measure ℝ))).symm.map_eq using 1
  rw [← hExp, exp_pair_withDensity]
  have he : (fun p : ℝ × ℝ ↦ ENNReal.ofReal (gammaPDFReal 1 1 p.1 * gammaPDFReal 1 1 p.2)) =
      fun p ↦ ENNReal.ofReal (magnitudeGaussianDensity (pack p)) := by
    funext p
    rfl
  rw [he, map_withDensity_comp _ pack hm (fun r ↦ ENNReal.ofReal (magnitudeGaussianDensity r))
    (by unfold magnitudeGaussianDensity; fun_prop), hVol]

def plantedMagnitudeDensity (M : ℕ) (u : Fin 2 → ℝ) : ℝ :=
  Real.exp (-(u 0 + u 1)) *
    ((sourceEta + (1 - sourceEta) / (u 0 + u 1)) /
      (sourceEpsilon M * sourceRadialNormalizer M))

theorem measurableSet_coneMagnitudeRegion (δ ε : ℝ) : MeasurableSet (coneMagnitudeRegion δ ε) := by
  unfold coneMagnitudeRegion
  have hs : Measurable (fun u : Fin 2 → ℝ ↦ u 0 + u 1) := by fun_prop
  have ht : Measurable (fun u : Fin 2 → ℝ ↦ |(u 0 - u 1) / (u 0 + u 1)|) := by fun_prop
  exact (measurableSet_le measurable_const hs).inter (measurableSet_le ht measurable_const)

theorem plantedMagnitudeLaw_eq_density {M : ℕ} (hM : 1 ≤ M) :
    plantedMagnitudeLaw M =
      (volume.restrict (coneMagnitudeRegion (sourceDelta M) (sourceEpsilon M))).withDensity
        (fun u ↦ ENNReal.ofReal (plantedMagnitudeDensity M u)) := by
  rw [plantedMagnitudeLaw, magnitudeGaussianLaw_eq_density,
    ← withDensity_mul _ (by unfold magnitudeGaussianDensity; fun_prop)
      (measurable_plantedMagnitudeWeight M).ennreal_ofReal,
    ← withDensity_indicator (measurableSet_coneMagnitudeRegion _ _)]
  congr 1
  funext u
  simp only [Pi.mul_apply]
  by_cases hu : u ∈ coneMagnitudeRegion (sourceDelta M) (sourceEpsilon M)
  · have hu' := coneMagnitudeRegion_nonneg (sourceDelta_pos M hM) (sourceEpsilon_le_one hM) hu
    rw [indicator_of_mem hu]
    change sourceDelta M ≤ u 0 + u 1 ∧ |(u 0 - u 1) / (u 0 + u 1)| ≤ sourceEpsilon M at hu
    simp only [plantedMagnitudeWeight, magnitudeCone, if_pos hu,
      magnitudeGaussianDensity, gammaPDFReal_one_one, if_pos hu'.1, if_pos hu'.2]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold plantedMagnitudeDensity
    rw [← Real.exp_add]
    congr 2
    ring
  · rw [indicator_of_notMem hu]
    change ¬(sourceDelta M ≤ u 0 + u 1 ∧ |(u 0 - u 1) / (u 0 + u 1)| ≤ sourceEpsilon M) at hu
    simp [plantedMagnitudeWeight, magnitudeCone, hu]

def plantedRadiusDensity (M : ℕ) (s : ℝ) : ℝ :=
  Real.exp (-s) * ((1 - sourceEta) + sourceEta * s) / sourceRadialNormalizer M

theorem plantedMagnitudeLaw_eq_coneMap {M : ℕ} (hM : 1 ≤ M) :
    plantedMagnitudeLaw M =
      ((volume.restrict (coneMagnitudeDomain (sourceDelta M) (sourceEpsilon M))).withDensity
        (fun p ↦ ENNReal.ofReal (plantedRadiusDensity M (p 0) / (2 * sourceEpsilon M)))).map
          coneMagnitudeMap := by
  rw [plantedMagnitudeLaw_eq_density hM,
    ← coneMagnitudeMap_withDensity (sourceDelta_pos M hM)
      (fun u ↦ ENNReal.ofReal (plantedMagnitudeDensity M u))
      (by unfold plantedMagnitudeDensity; fun_prop)]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_coneMagnitudeDomain (sourceDelta M) (sourceEpsilon M))]
    with p hp
  have hs := (sourceDelta_pos M hM).trans_le hp.1
  rw [← ENNReal.ofReal_mul (div_nonneg hs.le (by norm_num))]
  congr 1
  have he : coneMagnitudeMap p 0 + coneMagnitudeMap p 1 = p 0 := by
    simp [coneMagnitudeMap]
    ring
  unfold plantedMagnitudeDensity plantedRadiusDensity
  rw [he]
  field_simp [hs.ne', (sourceRadialNormalizer_pos M).ne']
  ring

end PlantedMagnitudeLaw

end NLA.FR05
