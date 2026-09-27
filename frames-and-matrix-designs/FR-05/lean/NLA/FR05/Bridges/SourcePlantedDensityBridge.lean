/-
The first coordinate-level identification between the sampler of Proposition
3.1 and the density law of Proposition 3.2.
-/
import NLA.FR05.Bridges.SourceRadialDensity

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- Pack the radial and imbalance coordinates as the two coordinate functions
used by `coneMagnitudeMap`. -/
def sourceMagnitudePairMap (p : ℝ × ℝ) : Fin 2 → ℝ := ![p.1, p.2]

@[fun_prop]
theorem measurable_sourceMagnitudePairMap : Measurable sourceMagnitudePairMap := by
  unfold sourceMagnitudePairMap
  fun_prop

theorem sourceMagnitudePairLaw_eq_density {M : ℕ} (hM : 1 ≤ M) :
    ((sourceRadialLaw sourceEta (sourceDelta M)).prod
      (sourceUniformInterval (-sourceEpsilon M) (sourceEpsilon M))).map
        sourceMagnitudePairMap =
      (volume.restrict (coneMagnitudeDomain (sourceDelta M) (sourceEpsilon M))).withDensity
        (fun p ↦ ENNReal.ofReal
          (plantedRadiusDensity M (p 0) / (2 * sourceEpsilon M))) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have hpair : sourceMagnitudePairMap = e.symm := by
    funext p
    rfl
  rw [hpair]
  apply (MeasurableEquiv.map_measurableEquiv_injective e)
  rw [MeasurableEquiv.map_map_symm]
  have hrad : Measurable (plantedRadiusDensity M) := by
    unfold plantedRadiusDensity
    fun_prop
  rw [sourceRadialLaw_sourceEta_eq_density hM,
    sourceUniformInterval_eq_density (by linarith [sourceEpsilon_pos M hM]),
    prod_withDensity hrad.ennreal_ofReal (by fun_prop)]
  have hdomain : coneMagnitudeDomain (sourceDelta M) (sourceEpsilon M) =
      e ⁻¹' ((Ici (sourceDelta M)) ×ˢ
        Icc (-sourceEpsilon M) (sourceEpsilon M)) := by
    ext p
    simp [coneMagnitudeDomain, e, abs_le]
  have hdensity : (fun q : Fin 2 → ℝ ↦ ENNReal.ofReal
      (plantedRadiusDensity M (q 0) / (2 * sourceEpsilon M))) =
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal
        (plantedRadiusDensity M p.1 / (2 * sourceEpsilon M))) ∘ e := by
    funext q
    rfl
  rw [hdensity]
  change _ = Measure.map e
    ((volume.restrict (coneMagnitudeDomain (sourceDelta M) (sourceEpsilon M))).withDensity
      (fun q ↦ ENNReal.ofReal
        (plantedRadiusDensity M (e q).1 / (2 * sourceEpsilon M))))
  rw [map_withDensity_comp _ _ e.measurable
    (fun p : ℝ × ℝ ↦ ENNReal.ofReal
      (plantedRadiusDensity M p.1 / (2 * sourceEpsilon M)))
    (by
      apply Measurable.ennreal_ofReal
      exact (hrad.comp measurable_fst).div_const _), hdomain,
    ← Measure.restrict_map e.measurable (measurableSet_Ici.prod measurableSet_Icc),
    (volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).map_eq,
    Measure.volume_eq_prod, Measure.prod_restrict]
  congr 1
  funext p
  rw [show sourceEpsilon M - -sourceEpsilon M = 2 * sourceEpsilon M by ring,
    mul_comm, ← ENNReal.ofReal_mul
      (inv_nonneg.mpr (mul_nonneg (by norm_num) (sourceEpsilon_pos M hM).le))]
  congr 1
  have hε : sourceEpsilon M ≠ 0 := (sourceEpsilon_pos M hM).ne'
  field_simp [hε]

/-- Applying the cone-coordinate map to the sampled radius and imbalance has
exactly the planted magnitude law. -/
theorem sourceSampledMagnitudes_eq_plantedMagnitudeLaw {M : ℕ} (hM : 1 ≤ M) :
    ((sourceRadialLaw sourceEta (sourceDelta M)).prod
      (sourceUniformInterval (-sourceEpsilon M) (sourceEpsilon M))).map
        (coneMagnitudeMap ∘ sourceMagnitudePairMap) =
      plantedMagnitudeLaw M := by
  rw [← Measure.map_map continuous_coneMagnitudeMap.measurable
      measurable_sourceMagnitudePairMap,
    sourceMagnitudePairLaw_eq_density hM,
    ← plantedMagnitudeLaw_eq_coneMap hM]

/-- Pack the two real phases as the two additive-circle phase coordinates. -/
def sourcePhasePairMap (p : ℝ × ℝ) : Fin 2 → ConePhase :=
  ![(p.1 : ConePhase), (p.2 : ConePhase)]

@[fun_prop]
theorem measurable_sourcePhasePairMap : Measurable sourcePhasePairMap := by
  unfold sourcePhasePairMap
  fun_prop

/-- The two independently sampled real phases have the product Haar law. -/
theorem sourceSampledPhases_eq_phaseVectorLaw :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod
      (sourceUniformInterval 0 (2 * Real.pi))).map sourcePhasePairMap =
      phaseVectorLaw := by
  let μ := sourceUniformInterval 0 (2 * Real.pi)
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ConePhase)
  let f : ℝ → ConePhase := fun x ↦ (x : ConePhase)
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  have hf : Measurable f := by
    exact AddCircle.measurable_mk'
  have hscalar : μ.map f = AddCircle.haarAddCircle := by
    exact sourceUniformInterval_zero_two_pi_map_conePhase
  have hpack : sourcePhasePairMap = e.symm ∘ Prod.map f f := by
    funext p
    rfl
  rw [hpack, ← Measure.map_map e.symm.measurable (hf.prodMap hf),
    ← Measure.map_prod_map μ μ hf hf, hscalar]
  unfold phaseVectorLaw
  exact (measurePreserving_piFinTwo
    (fun _ : Fin 2 ↦ (AddCircle.haarAddCircle : Measure ConePhase))).symm.map_eq

/-- Convert the four scalar sampling coordinates to magnitudes and phases. -/
def sourceScalarPolarMap (q : SourcePlantedScalars) :
    (Fin 2 → ℝ) × (Fin 2 → ConePhase) :=
  (coneMagnitudeMap (sourceMagnitudePairMap (q.1, q.2.1)),
    sourcePhasePairMap q.2.2)

@[fun_prop]
theorem measurable_sourceScalarPolarMap : Measurable sourceScalarPolarMap := by
  unfold sourceScalarPolarMap
  fun_prop

/-- The scalar sampler, after polar reconstruction, is precisely the
two-coordinate planted density law. -/
theorem sourceScalarLaw_map_polar_eq_sourcePlantedDensityLaw {M : ℕ}
    (hM : 1 ≤ M) :
    (sourceScalarLaw sourceEta (sourceDelta M) (sourceEpsilon M)).map
      sourceScalarPolarMap = (plantedMagnitudeLaw M).prod phaseVectorLaw := by
  let : IsProbabilityMeasure (sourceRadialLaw sourceEta (sourceDelta M)) :=
    isProbabilityMeasure_sourceRadialLaw sourceEta_pos.le sourceEta_lt_one
  let : IsProbabilityMeasure
      (sourceUniformInterval (-sourceEpsilon M) (sourceEpsilon M)) :=
    isProbabilityMeasure_sourceUniformInterval (by linarith [sourceEpsilon_pos M hM])
  let : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let e : SourcePlantedScalars ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc.symm
  let h : (ℝ × ℝ) × (ℝ × ℝ) → (Fin 2 → ℝ) × (Fin 2 → ConePhase) :=
    Prod.map (coneMagnitudeMap ∘ sourceMagnitudePairMap) sourcePhasePairMap
  have hh : Measurable h := by
    exact continuous_coneMagnitudeMap.measurable.comp measurable_sourceMagnitudePairMap |>.prodMap
      measurable_sourcePhasePairMap
  have hcomp : sourceScalarPolarMap = h ∘ e := by
    funext q
    rfl
  rw [hcomp, ← Measure.map_map hh e.measurable]
  unfold sourceScalarLaw
  rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map,
    ← Measure.map_prod_map _ _
      (continuous_coneMagnitudeMap.measurable.comp measurable_sourceMagnitudePairMap)
      measurable_sourcePhasePairMap,
    sourceSampledMagnitudes_eq_plantedMagnitudeLaw hM,
    sourceSampledPhases_eq_phaseVectorLaw]

/-- Reconstructing complex coordinates from the scalar sampler has precisely
the planted two-coordinate density law. -/
theorem sourceScalarLaw_map_phaseVector_eq_sourcePlantedDensityLaw {M : ℕ}
    (hM : 1 ≤ M) :
    (sourceScalarLaw sourceEta (sourceDelta M) (sourceEpsilon M)).map
      (phaseVectorMap ∘ sourceScalarPolarMap) = sourcePlantedDensityLaw M := by
  change (sourceScalarLaw sourceEta (sourceDelta M) (sourceEpsilon M)).map
      (phaseVectorMap ∘ sourceScalarPolarMap) = sourceDensityLaw .planted M
  rw [← Measure.map_map continuous_phaseVectorMap.measurable
      measurable_sourceScalarPolarMap,
    sourceScalarLaw_map_polar_eq_sourcePlantedDensityLaw hM,
    ← sourcePlantedDensityLaw_eq_polar hM]

/-- Join a two-coordinate head to an independent Gaussian tail. -/
def sourceHeadTailJoin {n : ℕ} (p : Signal 2 × Signal n) : Signal (n + 2) :=
  joinTwo (p.1 0) (p.1 1) p.2

theorem measurable_sourceHeadTailJoin {n : ℕ} : Measurable (sourceHeadTailJoin (n := n)) := by
  apply measurable_pi_lambda
  intro j
  by_cases hzero : j.1 = 0
  · simp only [sourceHeadTailJoin, joinTwo, dif_pos hzero]
    fun_prop
  by_cases hone : j.1 = 1
  · simp only [sourceHeadTailJoin, joinTwo, dif_neg hzero, dif_pos hone]
    fun_prop
  · let k : Fin n := ⟨j.1 - 2, by lia⟩
    simp only [sourceHeadTailJoin, joinTwo, dif_neg hzero, dif_neg hone]
    fun_prop

/-- Apply polar reconstruction to the scalar part of a source coordinate. -/
def sourceCoordinatePolarMap {n : ℕ} (p : SourcePlantedCoordinates n) :
    Signal 2 × Signal n := (phaseVectorMap (sourceScalarPolarMap p.1), p.2)

theorem measurable_sourceCoordinatePolarMap {n : ℕ} :
    Measurable (sourceCoordinatePolarMap (n := n)) := by
  unfold sourceCoordinatePolarMap
  exact ((continuous_phaseVectorMap.measurable.comp measurable_sourceScalarPolarMap).comp
    measurable_fst).prodMk measurable_snd

theorem sourcePlantedColumn_eq_sourceHeadTailJoin {n : ℕ}
    (p : SourcePlantedCoordinates n) :
    sourcePlantedColumn p = sourceHeadTailJoin (sourceCoordinatePolarMap p) := by
  ext i
  by_cases hzero : i.1 = 0
  · simp [sourcePlantedColumn, sourceHeadTailJoin, sourceCoordinatePolarMap,
      sourceScalarPolarMap, sourceMagnitudePairMap, sourcePhasePairMap,
      phaseVectorMap, coneMagnitudeMap, conePhasePoint,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, joinTwo, hzero]
  by_cases hone : i.1 = 1
  · simp [sourcePlantedColumn, sourceHeadTailJoin, sourceCoordinatePolarMap,
      sourceScalarPolarMap, sourceMagnitudePairMap, sourcePhasePairMap,
      phaseVectorMap, coneMagnitudeMap, conePhasePoint,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, joinTwo, hone]
  · simp [sourcePlantedColumn, sourceHeadTailJoin, sourceCoordinatePolarMap,
      joinTwo, hzero, hone]

/-- The source's sampled planted column is the density-law head joined to an
independent standard complex-Gaussian tail. -/
theorem sourcePlantedColumnLaw_eq_density_head_tail {M n : ℕ} (hM : 1 ≤ M) :
    sourcePlantedColumnLaw sourceEta (sourceDelta M) (sourceEpsilon M) n =
      ((sourceDensityLaw .planted M).prod (standardComplexGaussianTail n)).map
        sourceHeadTailJoin := by
  let : IsProbabilityMeasure
      (sourceScalarLaw sourceEta (sourceDelta M) (sourceEpsilon M)) :=
    isProbabilityMeasure_sourceScalarLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM)
  change sourcePlantedColumnLaw sourceEta (sourceDelta M) (sourceEpsilon M) n =
    ((sourcePlantedDensityLaw M).prod (standardComplexGaussianTail n)).map sourceHeadTailJoin
  unfold sourcePlantedColumnLaw sourceCoordinateLaw
  rw [show sourcePlantedColumn = sourceHeadTailJoin ∘ sourceCoordinatePolarMap by
    funext p
    exact sourcePlantedColumn_eq_sourceHeadTailJoin p,
    ← Measure.map_map measurable_sourceHeadTailJoin measurable_sourceCoordinatePolarMap]
  change (Measure.map (Prod.map (phaseVectorMap ∘ sourceScalarPolarMap) id)
    ((sourceScalarLaw sourceEta (sourceDelta M) (sourceEpsilon M)).prod
      (standardComplexGaussianTail n))).map sourceHeadTailJoin = _
  rw [← Measure.map_prod_map _ _
      (continuous_phaseVectorMap.measurable.comp measurable_sourceScalarPolarMap)
      measurable_id,
    sourceScalarLaw_map_phaseVector_eq_sourcePlantedDensityLaw hM,
    Measure.map_id]

end NLA.FR05
