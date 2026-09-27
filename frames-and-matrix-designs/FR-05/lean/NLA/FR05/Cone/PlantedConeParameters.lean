import NLA.FR05.Densities.PlantedPolarLaw

/-!
# Planted cone and polar parameters

The sections develop `PlantedConeParameters`, `ConePolarParameters`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section PlantedConeParameters

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

theorem lintegral_coneMagnitudeDomain (δ ε : ℝ)
    (f : (Fin 2 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in coneMagnitudeDomain δ ε, f p) =
      ∫⁻ s in Ici δ, ∫⁻ t in Icc (-ε) ε, f ![s, t] := by
  let pack : ℝ × ℝ → Fin 2 → ℝ := fun p ↦ ![p.1, p.2]
  have hm : Measurable pack := by dsimp [pack]; fun_prop
  have hVol : (volume : Measure (ℝ × ℝ)).map pack = volume := by
    rw [Measure.volume_eq_prod]
    convert! (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ (volume : Measure ℝ))).symm.map_eq using 1
  rw [← lintegral_indicator (measurableSet_coneMagnitudeDomain δ ε), ← hVol,
    lintegral_map (hf.indicator (measurableSet_coneMagnitudeDomain δ ε)) hm]
  have he : (fun p : ℝ × ℝ ↦ (coneMagnitudeDomain δ ε).indicator f (pack p)) =
      ((Ici δ) ×ˢ Icc (-ε) ε).indicator (fun p : ℝ × ℝ ↦ f (pack p)) := by
    funext p
    simp [coneMagnitudeDomain, pack, Set.indicator, abs_le]
  rw [he, lintegral_indicator (measurableSet_Ici.prod measurableSet_Icc),
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by exact (hf.comp hm).aemeasurable)]

theorem lintegral_plantedMagnitudeLaw {M : ℕ} (hM : 1 ≤ M)
    (f : (Fin 2 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, f u ∂plantedMagnitudeLaw M) =
      ∫⁻ s in Ici (sourceDelta M), ∫⁻ t in Icc (-sourceEpsilon M) (sourceEpsilon M),
        ENNReal.ofReal (plantedRadiusDensity M s / (2 * sourceEpsilon M)) *
          f (coneMagnitudeMap ![s, t]) := by
  rw [plantedMagnitudeLaw_eq_coneMap hM,
    lintegral_map hf continuous_coneMagnitudeMap.measurable,
    lintegral_withDensity_eq_lintegral_mul _
      (g := fun p ↦ f (coneMagnitudeMap p))
      (by unfold plantedRadiusDensity; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]
  rw [lintegral_coneMagnitudeDomain _ _ _ (by unfold plantedRadiusDensity; fun_prop)]
  rfl

theorem lintegral_sourcePlantedDensityLaw_parameters {M : ℕ} (hM : 1 ≤ M)
    (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂sourceDensityLaw .planted M) =
      ∫⁻ s in Ici (sourceDelta M), ∫⁻ t in Icc (-sourceEpsilon M) (sourceEpsilon M),
        ENNReal.ofReal (plantedRadiusDensity M s / (2 * sourceEpsilon M)) *
          ∫⁻ θ, f (phaseVectorMap (coneMagnitudeMap ![s, t], θ)) ∂phaseVectorLaw := by
  rw [sourcePlantedDensityLaw_eq_polar hM,
    lintegral_map hf continuous_phaseVectorMap.measurable,
    lintegral_prod (fun p ↦ f (phaseVectorMap p))
      (by exact (hf.comp continuous_phaseVectorMap.measurable).aemeasurable),
    lintegral_plantedMagnitudeLaw hM _
      (by apply Measurable.lintegral_prod_right; fun_prop)]

end PlantedConeParameters

section ConePolarParameters

open MeasureTheory ProbabilityTheory Complex Real Set
open scoped ENNReal

theorem lintegral_expMeasure_one (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, f s ∂expMeasure 1) =
      ∫⁻ s in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * f s := by
  change (∫⁻ s, f s ∂volume.withDensity (fun s ↦ ENNReal.ofReal (gammaPDFReal 1 1 s))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_gammaPDFReal 1 1).ennreal_ofReal hf]
  have he (s : ℝ) : ENNReal.ofReal (gammaPDFReal 1 1 s) * f s =
      (Ici (0 : ℝ)).indicator (fun s ↦ ENNReal.ofReal (Real.exp (-s)) * f s) s := by
    by_cases hs : 0 ≤ s <;> simp [gammaPDFReal_one_one, Set.indicator, hs]
  simp only [Pi.mul_apply]
  simp_rw [he]
  exact lintegral_indicator measurableSet_Ici _

def coneRadiusDensity (s : ℝ) : ℝ :=
  Real.exp (-s) * ((1 - sourceEta) + sourceEta * s)

theorem lintegral_coneScalarMeasure (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂coneScalarMeasure) =
      ∫⁻ s in Ici (0 : ℝ), ENNReal.ofReal (coneRadiusDensity s) *
        ∫⁻ θ : ConePhase, f (scalarPolarMap (s, θ)) ∂AddCircle.haarAddCircle := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  rw [coneScalarMeasure, lintegral_withDensity_eq_lintegral_mul _
    continuous_coneRadialWeight.measurable.ennreal_ofReal hf,
    scalarComplexGaussian_eq_polar,
    lintegral_map (continuous_coneRadialWeight.measurable.ennreal_ofReal.mul hf)
      continuous_scalarPolarMap.measurable,
    lintegral_prod _ (by apply Measurable.aemeasurable; dsimp; fun_prop),
    lintegral_expMeasure_one _ (by apply Measurable.lintegral_prod_right; fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro s hs
  have hw (θ : ConePhase) :
      coneRadialWeight (scalarPolarMap (s, θ)) = (1 - sourceEta) + sourceEta * s := by
    simp [coneRadialWeight, scalarPolarMap, Complex.normSq_eq_norm_sq, Real.sq_sqrt hs]
  simp only [Pi.mul_apply]
  simp_rw [hw]
  rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem phaseVectorLaw_eq_relative :
    phaseVectorLaw =
      (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle).map
        (fun p : ConePhase × ConePhase ↦ ![p.1, p.1 + p.2]) := by
  unfold phaseVectorLaw
  have hp := (measurePreserving_piFinTwo
    (fun _ : Fin 2 ↦ (AddCircle.haarAddCircle : Measure ConePhase))).symm.map_eq
  have hs := (measurePreserving_prod_add_right
    (AddCircle.haarAddCircle : Measure ConePhase) AddCircle.haarAddCircle).map_eq
  rw [← hs, Measure.map_map
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ConePhase)).symm.measurable (by fun_prop)] at hp
  symm
  convert hp using 1
  congr 1
  funext p
  ext i
  fin_cases i <;> simp [add_comm]

theorem phaseVectorMap_coneMagnitude {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (θ ψ : ConePhase) :
    phaseVectorMap (coneMagnitudeMap ![s, t], ![θ, θ + ψ]) =
      conePoint t (ψ, scalarPolarMap (s, θ)) := by
  have hp : s * (1 + t) / 2 = s * ((1 + t) / 2) := by ring
  have hm : s * (1 - t) / 2 = s * ((1 - t) / 2) := by ring
  rw [conePoint_eq]
  ext i
  fin_cases i <;>
    simp [phaseVectorMap, coneMagnitudeMap, scalarPolarMap, coneDirection, hp, hm,
      Real.sqrt_mul hs, Complex.ofReal_mul, conePhasePoint_add] <;> ring

theorem lintegral_phaseVector_cone {s : ℝ} (hs : 0 ≤ s) (t : ℝ)
    (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ θ, f (phaseVectorMap (coneMagnitudeMap ![s, t], θ)) ∂phaseVectorLaw) =
      ∫⁻ ψ : ConePhase, ∫⁻ θ : ConePhase, f (conePoint t (ψ, scalarPolarMap (s, θ)))
        ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  rw [phaseVectorLaw_eq_relative,
    lintegral_map (by fun_prop) (by fun_prop),
    lintegral_prod _ (by apply Measurable.aemeasurable; fun_prop)]
  simp_rw [phaseVectorMap_coneMagnitude hs t]
  exact lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)

theorem lintegral_coneMeasure_parameters (t : ℝ) (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂coneMeasure t) =
      ∫⁻ s in Ici (0 : ℝ), ENNReal.ofReal (coneRadiusDensity s) *
        ∫⁻ θ, f (phaseVectorMap (coneMagnitudeMap ![s, t], θ)) ∂phaseVectorLaw := by
  rw [coneMeasure, lintegral_map hf (continuous_conePoint t).measurable,
    lintegral_prod _ (by exact (hf.comp (continuous_conePoint t).measurable).aemeasurable)]
  have hs (ψ : ConePhase) :
      (∫⁻ x, f (conePoint t (ψ, x)) ∂coneScalarMeasure) =
        ∫⁻ s in Ici (0 : ℝ), ENNReal.ofReal (coneRadiusDensity s) *
          ∫⁻ θ : ConePhase, f (conePoint t (ψ, scalarPolarMap (s, θ))) ∂AddCircle.haarAddCircle :=
    lintegral_coneScalarMeasure _ (by fun_prop)
  simp_rw [hs]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    apply Measurable.mul
    · unfold coneRadiusDensity
      fun_prop
    · apply Measurable.lintegral_prod_right
      fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro s hs
  dsimp only
  rw [lintegral_phaseVector_cone hs t f hf, lintegral_const_mul _ (by
    apply Measurable.lintegral_prod_right
    fun_prop)]

end ConePolarParameters

end NLA.FR05
