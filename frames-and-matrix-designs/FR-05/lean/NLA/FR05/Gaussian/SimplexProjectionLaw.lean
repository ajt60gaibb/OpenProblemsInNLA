import NLA.FR05.Gaussian.GammaSimplexLaw

/-!
# Simplex projections and sphere projection densities

The sections develop `SimplexProjectionLaw`, `SphereProjectionDensity`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section SimplexProjectionLaw

open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal

def simplexMagnitudeWeight (n : ℕ) (r : Fin 2 → ℝ) : ℝ :=
  ((n + 1) * (n + 2) : ℝ) * (1 - r 0 - r 1) ^ n

def simplexMagnitudeLaw (n : ℕ) : Measure (Fin 2 → ℝ) :=
  (volume.restrict openSimplex).withDensity (fun r ↦ ENNReal.ofReal (simplexMagnitudeWeight n r))

instance (n : ℕ) : SFinite (simplexMagnitudeLaw n) := by
  unfold simplexMagnitudeLaw
  infer_instance

def gammaTripleWeight (n : ℕ) (r : Fin 3 → ℝ) : ℝ :=
  r 2 ^ n / n.factorial * Real.exp (-(r 0 + r 1 + r 2))

def gammaTripleLaw (n : ℕ) : Measure (Fin 3 → ℝ) :=
  (volume.restrict positiveOctant).withDensity (fun r ↦ ENNReal.ofReal (gammaTripleWeight n r))

def simplexJointLaw (n : ℕ) : Measure (Fin 3 → ℝ) :=
  (volume.restrict simplexRadiusDomain).withDensity
    (fun r ↦ ENNReal.ofReal (gammaNatWeight (n + 2) (r 2)) *
      ENNReal.ofReal (simplexMagnitudeWeight n ![r 0, r 1]))

@[fun_prop]
theorem continuous_simplexMagnitudeWeight (n : ℕ) : Continuous (simplexMagnitudeWeight n) := by
  unfold simplexMagnitudeWeight
  fun_prop

@[fun_prop]
theorem continuous_gammaTripleWeight (n : ℕ) : Continuous (gammaTripleWeight n) := by
  unfold gammaTripleWeight
  fun_prop

theorem positiveOctant_eq_triple_preimage :
    positiveOctant = radiusTripleEquiv ⁻¹' (Ioi (0 : ℝ) ×ˢ positiveQuadrant) := by
  ext r
  simp only [positiveOctant, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
    radiusTripleEquiv_apply, Set.mem_Ioi, positiveQuadrant, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · intro h
    exact ⟨h 2, h 0, h 1⟩
  · rintro ⟨h2, h0, h1⟩ i
    fin_cases i <;> assumption

theorem simplexRadiusDomain_eq_triple_preimage :
    simplexRadiusDomain = radiusTripleEquiv ⁻¹' (Ioi (0 : ℝ) ×ˢ openSimplex) := by
  ext r
  simp [simplexRadiusDomain, radiusTripleEquiv_apply, openSimplex, and_comm, and_assoc]

theorem gammaTripleLaw_map_split (n : ℕ) :
    (gammaTripleLaw n).map radiusTripleEquiv =
      (gammaMeasure (n + 1) 1).prod magnitudeGaussianLaw := by
  rw [gammaMeasure_nat_eq_density, magnitudeGaussianLaw_eq_quadrant_density,
    ← radiusTripleEquiv_weighted (Ioi 0) positiveQuadrant measurableSet_Ioi
      measurableSet_positiveQuadrant (fun s ↦ ENNReal.ofReal (gammaNatWeight n s))
      (fun r ↦ ENNReal.ofReal (Real.exp (-(r 0 + r 1)))) (by fun_prop) (by fun_prop)]
  congr 1
  rw [← positiveOctant_eq_triple_preimage]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_positiveOctant] with r hr
  simp only [radiusTripleEquiv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← ENNReal.ofReal_mul (gammaNatWeight_nonneg n (hr 2).le)]
  congr 1
  unfold gammaTripleWeight gammaNatWeight
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem simplexJointLaw_map_split (n : ℕ) :
    (simplexJointLaw n).map radiusTripleEquiv =
      (gammaMeasure ((n + 2 : ℕ) + 1) 1).prod (simplexMagnitudeLaw n) := by
  rw [gammaMeasure_nat_eq_density]
  unfold simplexJointLaw simplexMagnitudeLaw
  rw [simplexRadiusDomain_eq_triple_preimage]
  have h := radiusTripleEquiv_weighted (Ioi 0) openSimplex measurableSet_Ioi
    measurableSet_openSimplex (fun s ↦ ENNReal.ofReal (gammaNatWeight (n + 2) s))
    (fun r ↦ ENNReal.ofReal (simplexMagnitudeWeight n r)) (by fun_prop) (by fun_prop)
  simpa only [radiusTripleEquiv_apply] using h

theorem simplex_joint_weight (n : ℕ) (p : Fin 3 → ℝ) :
    p 2 ^ 2 * gammaTripleWeight n (simplexRadiusMap p) =
      gammaNatWeight (n + 2) (p 2) * simplexMagnitudeWeight n ![p 0, p 1] := by
  have he : p 2 * p 0 + p 2 * p 1 + p 2 * (1 - p 0 - p 1) = p 2 := by ring
  simp only [gammaTripleWeight, simplexRadiusMap, gammaNatWeight, simplexMagnitudeWeight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
  change p 2 ^ 2 * ((p 2 * (1 - p 0 - p 1)) ^ n / n.factorial *
    Real.exp (-(p 2 * p 0 + p 2 * p 1 + p 2 * (1 - p 0 - p 1)))) = _
  rw [he]
  simp only [mul_pow, pow_add, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem simplexJointLaw_map_radius (n : ℕ) :
    (simplexJointLaw n).map simplexRadiusMap = gammaTripleLaw n := by
  have hw : simplexJointLaw n =
      (volume.restrict simplexRadiusDomain).withDensity
        (fun p ↦ ENNReal.ofReal (p 2 ^ 2) *
          ENNReal.ofReal (gammaTripleWeight n (simplexRadiusMap p))) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_simplexRadiusDomain] with p hp
    rw [← ENNReal.ofReal_mul (gammaNatWeight_nonneg (n + 2) hp.2.2.2.le),
      ← ENNReal.ofReal_mul (sq_nonneg _), simplex_joint_weight]
  have hm :
      (volume.restrict simplexRadiusDomain).withDensity
        (fun p ↦ ENNReal.ofReal (p 2 ^ 2) *
          ENNReal.ofReal (gammaTripleWeight n (simplexRadiusMap p))) =
      ((volume.restrict simplexRadiusDomain).withDensity
        (fun p ↦ ENNReal.ofReal (p 2 ^ 2))).withDensity
        (fun p ↦ ENNReal.ofReal (gammaTripleWeight n (simplexRadiusMap p))) :=
    withDensity_mul _ (by fun_prop) (by fun_prop)
  rw [hw, hm, map_withDensity_comp _ _ continuous_simplexRadiusMap.measurable _
    (continuous_gammaTripleWeight n).measurable.ennreal_ofReal, simplexRadiusMap_volume]
  rfl

def normalizedMagnitudes (p : ℝ × (Fin 2 → ℝ)) : Fin 2 → ℝ :=
  fun i ↦ p.2 i / (p.2 0 + p.2 1 + p.1)

@[fun_prop]
theorem measurable_normalizedMagnitudes : Measurable normalizedMagnitudes := by
  unfold normalizedMagnitudes
  fun_prop

theorem gamma_pair_normalizedMagnitudes (n : ℕ) :
    ((gammaMeasure (n + 1) 1).prod magnitudeGaussianLaw).map normalizedMagnitudes =
      simplexMagnitudeLaw n := by
  let : IsProbabilityMeasure (gammaMeasure ((n + 2 : ℕ) + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one
  rw [← gammaTripleLaw_map_split n,
    Measure.map_map measurable_normalizedMagnitudes radiusTripleEquiv.measurable,
    ← simplexJointLaw_map_radius n,
    Measure.map_map (measurable_normalizedMagnitudes.comp radiusTripleEquiv.measurable)
      continuous_simplexRadiusMap.measurable]
  have he : (simplexJointLaw n).map
      ((normalizedMagnitudes ∘ radiusTripleEquiv) ∘ simplexRadiusMap) =
      (simplexJointLaw n).map (Prod.snd ∘ radiusTripleEquiv) := by
    apply Measure.map_congr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_simplexRadiusDomain] with p hp
    change normalizedMagnitudes (radiusTripleEquiv (simplexRadiusMap p)) =
      (radiusTripleEquiv p).2
    have hi := simplexRadiusInverse_map hp.2.2.2.ne'
    ext i
    fin_cases i
    · simpa [normalizedMagnitudes, radiusTripleEquiv_apply, simplexRadiusInverse]
        using congrFun hi 0
    · simpa [normalizedMagnitudes, radiusTripleEquiv_apply, simplexRadiusInverse]
        using congrFun hi 1
  rw [he, ← Measure.map_map measurable_snd radiusTripleEquiv.measurable,
    simplexJointLaw_map_split, Measure.map_snd_prod]
  rw [measure_univ, one_smul]

end SimplexProjectionLaw

section SphereProjectionDensity

open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal

def sphereRadialWeight (n : ℕ) (s : ℝ) : ℝ :=
  if s < 1 then ((n + 1) * (n + 2) : ℝ) * (1 - s) ^ n * Real.exp s else 0

@[fun_prop]
theorem measurable_sphereRadialWeight (n : ℕ) : Measurable (sphereRadialWeight n) := by
  unfold sphereRadialWeight
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem sphereRadialWeight_nonneg (n : ℕ) (s : ℝ) : 0 ≤ sphereRadialWeight n s := by
  unfold sphereRadialWeight
  split_ifs with h <;> positivity

theorem simplexMagnitudeLaw_eq_gaussian_weight (n : ℕ) :
    simplexMagnitudeLaw n = magnitudeGaussianLaw.withDensity
      (fun r ↦ ENNReal.ofReal (sphereRadialWeight n (r 0 + r 1))) := by
  rw [magnitudeGaussianLaw_eq_quadrant_density]
  have hm :
      ((volume.restrict positiveQuadrant).withDensity
        (fun r ↦ ENNReal.ofReal (Real.exp (-(r 0 + r 1))))).withDensity
        (fun r ↦ ENNReal.ofReal (sphereRadialWeight n (r 0 + r 1))) =
      (volume.restrict positiveQuadrant).withDensity
        (fun r ↦ ENNReal.ofReal (Real.exp (-(r 0 + r 1))) *
          ENNReal.ofReal (sphereRadialWeight n (r 0 + r 1))) :=
    (withDensity_mul _ (by fun_prop) (by fun_prop)).symm
  rw [hm]
  unfold simplexMagnitudeLaw
  rw [← withDensity_indicator measurableSet_openSimplex,
    ← withDensity_indicator measurableSet_positiveQuadrant]
  congr 1
  funext r
  by_cases hp : r ∈ positiveQuadrant
  · by_cases hs : r 0 + r 1 < 1
    · have ht : r ∈ openSimplex := ⟨hp.1, hp.2, hs⟩
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      unfold simplexMagnitudeWeight sphereRadialWeight
      rw [if_pos hs]
      have he : Real.exp (-(r 0 + r 1)) * Real.exp (r 0 + r 1) = 1 := by
        rw [← Real.exp_add]
        simp
      have hx : 1 - (r 0 + r 1) = 1 - r 0 - r 1 := by ring
      rw [hx]
      calc
        _ = ((n + 1) * (n + 2) : ℝ) * (1 - r 0 - r 1) ^ n * 1 := by ring
        _ = _ := by rw [← he]; ring
    · have ht : r ∉ openSimplex := fun h ↦ hs h.2.2
      simp [Set.indicator_of_notMem ht, Set.indicator_of_mem hp, sphereRadialWeight, hs]
  · have ht : r ∉ openSimplex := fun h ↦ hp ⟨h.1, h.2.1⟩
    simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp]

def sphereProjectionLaw (n : ℕ) : Measure (Signal 2) :=
  (standardComplexGaussianTail 2).withDensity
    (fun z ↦ ENNReal.ofReal (sphereRadialWeight n (signalEnergy z)))

theorem sphereProjectionLaw_eq_polar (n : ℕ) :
    sphereProjectionLaw n = ((simplexMagnitudeLaw n).prod phaseVectorLaw).map phaseVectorMap := by
  unfold sphereProjectionLaw
  rw [standardComplexGaussianTail_two_polar,
    ← map_withDensity_comp _ _ continuous_phaseVectorMap.measurable _
      (show Measurable (fun z : Signal 2 ↦
        ENNReal.ofReal (sphereRadialWeight n (signalEnergy z))) by
          apply Measurable.ennreal_ofReal
          apply (measurable_sphereRadialWeight n).comp
          apply Continuous.measurable
          unfold signalEnergy squaredEuclideanNorm
          fun_prop),
    simplexMagnitudeLaw_eq_gaussian_weight,
    prod_withDensity_left (by fun_prop)]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_magnitudeGaussianLaw_nonneg] with p hp
  congr 1
  congr 1
  simp [signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two, phaseVectorMap_normSq _ _ hp]

end SphereProjectionDensity

end NLA.FR05
