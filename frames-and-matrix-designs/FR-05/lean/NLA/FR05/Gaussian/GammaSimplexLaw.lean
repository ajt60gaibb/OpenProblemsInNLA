import NLA.FR05.Densities.PlantedPolarLaw

/-!
# Gamma-simplex laws and radius coordinates

The sections develop `SimplexRadiusCoordinates`, `GammaSimplexLaw`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section SimplexRadiusCoordinates

open MeasureTheory Matrix Set
open scoped ENNReal

def simplexRadiusMap (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 2 * p 0, p 2 * p 1, p 2 * (1 - p 0 - p 1)]

def simplexRadiusInverse (r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![r 0 / (r 0 + r 1 + r 2), r 1 / (r 0 + r 1 + r 2), r 0 + r 1 + r 2]

def simplexRadiusDerivative (p : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' !![p 2, 0, p 0; 0, p 2, p 1; -p 2, -p 2, 1 - p 0 - p 1]).toContinuousLinearMap

@[fun_prop]
theorem continuous_simplexRadiusMap : Continuous simplexRadiusMap := by
  unfold simplexRadiusMap
  fun_prop

@[fun_prop]
theorem measurable_simplexRadiusInverse : Measurable simplexRadiusInverse := by
  unfold simplexRadiusInverse
  fun_prop

theorem hasFDerivAt_simplexRadiusMap (p : Fin 3 → ℝ) :
    HasFDerivAt simplexRadiusMap (simplexRadiusDerivative p) p := by
  let e (i : Fin 3) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i
  let d0 := p 2 • e 0 + p 0 • e 2
  let d1 := p 2 • e 1 + p 1 • e 2
  let d2 := p 2 • (0 - e 0 - e 1) + (1 - p 0 - p 1) • e 2
  have h0 : HasFDerivAt (fun x : Fin 3 → ℝ ↦ x 2 * x 0) d0 p :=
    (hasFDerivAt_apply (𝕜 := ℝ) 2 p).mul (hasFDerivAt_apply 0 p)
  have h1 : HasFDerivAt (fun x : Fin 3 → ℝ ↦ x 2 * x 1) d1 p :=
    (hasFDerivAt_apply (𝕜 := ℝ) 2 p).mul (hasFDerivAt_apply 1 p)
  have h2 : HasFDerivAt (fun x : Fin 3 → ℝ ↦ x 2 * (1 - x 0 - x 1)) d2 p :=
    (hasFDerivAt_apply (𝕜 := ℝ) 2 p).mul
      (((hasFDerivAt_const (1 : ℝ) p).sub (hasFDerivAt_apply 0 p)).sub (hasFDerivAt_apply 1 p))
  have h : ∀ i : Fin 3, HasFDerivAt
      (![fun x : Fin 3 → ℝ ↦ x 2 * x 0, fun x ↦ x 2 * x 1,
        fun x ↦ x 2 * (1 - x 0 - x 1)] i) (![d0, d1, d2] i) p := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  convert! hasFDerivAt_pi.mpr h using 1
  · funext x i
    fin_cases i <;> rfl
  · ext x i
    fin_cases i <;>
      simp [d0, d1, d2, e, simplexRadiusDerivative, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    all_goals ring

theorem simplexRadiusDerivative_det (p : Fin 3 → ℝ) :
    (simplexRadiusDerivative p).det = p 2 ^ 2 := by
  simp [simplexRadiusDerivative, ContinuousLinearMap.det, LinearMap.det_toLin',
    Matrix.det_fin_three]
  ring

theorem simplexRadiusInverse_map {p : Fin 3 → ℝ} (hp : p 2 ≠ 0) :
    simplexRadiusInverse (simplexRadiusMap p) = p := by
  have he : p 2 * p 0 + p 2 * p 1 + p 2 * (1 - p 0 - p 1) = p 2 := by ring
  ext i
  fin_cases i <;> simp [simplexRadiusInverse, simplexRadiusMap, he, hp]

theorem simplexRadiusMap_inverse {r : Fin 3 → ℝ} (hr : r 0 + r 1 + r 2 ≠ 0) :
    simplexRadiusMap (simplexRadiusInverse r) = r := by
  ext i
  fin_cases i <;> simp [simplexRadiusMap, simplexRadiusInverse] <;> field_simp [hr]
  all_goals ring

def simplexRadiusDomain : Set (Fin 3 → ℝ) :=
  {p | 0 < p 0 ∧ 0 < p 1 ∧ p 0 + p 1 < 1 ∧ 0 < p 2}

def positiveOctant : Set (Fin 3 → ℝ) := {r | ∀ i, 0 < r i}

theorem measurableSet_simplexRadiusDomain : MeasurableSet simplexRadiusDomain := by
  unfold simplexRadiusDomain
  measurability

theorem measurableSet_positiveOctant : MeasurableSet positiveOctant := by
  unfold positiveOctant
  measurability

theorem simplexRadiusMap_injOn : InjOn simplexRadiusMap simplexRadiusDomain := by
  intro p hp q hq he
  have h := congrArg simplexRadiusInverse he
  rwa [simplexRadiusInverse_map hp.2.2.2.ne', simplexRadiusInverse_map hq.2.2.2.ne'] at h

theorem simplexRadiusMap_image :
    simplexRadiusMap '' simplexRadiusDomain = positiveOctant := by
  ext r
  constructor
  · rintro ⟨p, hp, rfl⟩ i
    fin_cases i
    · exact mul_pos hp.2.2.2 hp.1
    · exact mul_pos hp.2.2.2 hp.2.1
    · exact mul_pos hp.2.2.2 (by linarith [hp.2.2.1])
  · intro hr
    have ht : 0 < r 0 + r 1 + r 2 := by linarith [hr 0, hr 1, hr 2]
    refine ⟨simplexRadiusInverse r, ?_, simplexRadiusMap_inverse ht.ne'⟩
    change 0 < r 0 / _ ∧ 0 < r 1 / _ ∧ r 0 / _ + r 1 / _ < 1 ∧ 0 < _
    refine ⟨div_pos (hr 0) ht, div_pos (hr 1) ht, ?_, ht⟩
    rw [← add_div, div_lt_one ht]
    linarith [hr 2]

theorem simplexRadiusMap_volume :
    ((volume.restrict simplexRadiusDomain).withDensity
      (fun p ↦ ENNReal.ofReal (p 2 ^ 2))).map simplexRadiusMap =
      volume.restrict positiveOctant := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure (Fin 3 → ℝ)) measurableSet_simplexRadiusDomain.nullMeasurableSet
    (fun p _ ↦ (hasFDerivAt_simplexRadiusMap p).hasFDerivWithinAt)
    simplexRadiusMap_injOn
  rw [simplexRadiusMap_image] at h
  simpa only [simplexRadiusDerivative_det, abs_sq] using h

end SimplexRadiusCoordinates

section GammaSimplexLaw

open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal

def radiusTripleEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 2

theorem radiusTripleEquiv_apply (r : Fin 3 → ℝ) :
    radiusTripleEquiv r = (r 2, ![r 0, r 1]) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem radiusTripleEquiv_symm_apply (p : ℝ × (Fin 2 → ℝ)) :
    radiusTripleEquiv.symm p = ![p.2 0, p.2 1, p.1] := by
  apply radiusTripleEquiv.injective
  rw [radiusTripleEquiv.apply_symm_apply, radiusTripleEquiv_apply]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem volumePreserving_radiusTripleEquiv : MeasurePreserving radiusTripleEquiv :=
  volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 2

theorem radiusTripleEquiv_weighted (s : Set ℝ) (t : Set (Fin 2 → ℝ))
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : ℝ → ℝ≥0∞) (g : (Fin 2 → ℝ) → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    ((volume.restrict (radiusTripleEquiv ⁻¹' (s ×ˢ t))).withDensity
      (fun r ↦ f (radiusTripleEquiv r).1 * g (radiusTripleEquiv r).2)).map radiusTripleEquiv =
      ((volume.restrict s).withDensity f).prod ((volume.restrict t).withDensity g) := by
  rw [map_withDensity_comp _ _ radiusTripleEquiv.measurable
    (fun p ↦ f p.1 * g p.2) (by fun_prop)]
  rw [← Measure.restrict_map radiusTripleEquiv.measurable (hs.prod ht),
    volumePreserving_radiusTripleEquiv.map_eq, Measure.volume_eq_prod,
    ← Measure.prod_restrict, prod_withDensity hf hg]

def positiveQuadrant : Set (Fin 2 → ℝ) := {r | 0 < r 0 ∧ 0 < r 1}

def openSimplex : Set (Fin 2 → ℝ) := {r | 0 < r 0 ∧ 0 < r 1 ∧ r 0 + r 1 < 1}

theorem measurableSet_positiveQuadrant : MeasurableSet positiveQuadrant := by
  unfold positiveQuadrant
  measurability

theorem measurableSet_openSimplex : MeasurableSet openSimplex := by
  unfold openSimplex
  measurability

def gammaNatWeight (n : ℕ) (s : ℝ) : ℝ :=
  s ^ n / n.factorial * Real.exp (-s)

@[fun_prop]
theorem continuous_gammaNatWeight (n : ℕ) : Continuous (gammaNatWeight n) := by
  unfold gammaNatWeight
  fun_prop

theorem gammaNatWeight_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ gammaNatWeight n s := by
  unfold gammaNatWeight
  positivity

theorem gammaMeasure_nat_eq_density (n : ℕ) :
    gammaMeasure (n + 1) 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun s ↦ ENNReal.ofReal (gammaNatWeight n s)) := by
  rw [restrict_Ioi_eq_restrict_Ici, ← withDensity_indicator measurableSet_Ici]
  unfold gammaMeasure
  congr 1
  funext s
  by_cases hs : 0 ≤ s
  · simp [gammaPDF, gammaPDFReal, Set.indicator, hs, Real.Gamma_nat_eq_factorial,
      gammaNatWeight, Real.rpow_natCast, div_eq_mul_inv, mul_assoc, mul_comm]
  · simp [gammaPDF, gammaPDFReal, Set.indicator, hs]

theorem expMeasure_one_eq_density :
    expMeasure 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun s ↦ ENNReal.ofReal (Real.exp (-s))) := by
  simpa [gammaNatWeight, expMeasure] using gammaMeasure_nat_eq_density 0

theorem magnitudeGaussianLaw_eq_quadrant_density :
    magnitudeGaussianLaw = (volume.restrict positiveQuadrant).withDensity
      (fun r ↦ ENNReal.ofReal (Real.exp (-(r 0 + r 1)))) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have he := (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ expMeasure 1)).map_eq
  have hv := (volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).map_eq
  have hs : positiveQuadrant = e ⁻¹' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := rfl
  apply (MeasurableEquiv.map_measurableEquiv_injective e)
  change magnitudeGaussianLaw.map e = _
  rw [show magnitudeGaussianLaw.map e = (expMeasure 1).prod (expMeasure 1) from he,
    expMeasure_one_eq_density, prod_withDensity (by fun_prop) (by fun_prop)]
  have hw : (fun r : Fin 2 → ℝ ↦ ENNReal.ofReal (Real.exp (-(r 0 + r 1)))) =
      (fun r ↦ ENNReal.ofReal (Real.exp (-(e r).1)) *
        ENNReal.ofReal (Real.exp (-(e r).2))) := by
    funext r
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp [e]
    ring
  rw [hw, map_withDensity_comp _ _ e.measurable _
    (show Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-p.1)) *
      ENNReal.ofReal (Real.exp (-p.2))) by fun_prop), hs,
    ← Measure.restrict_map e.measurable (measurableSet_Ioi.prod measurableSet_Ioi),
    hv, Measure.volume_eq_prod, Measure.prod_restrict]

end GammaSimplexLaw

end NLA.FR05
