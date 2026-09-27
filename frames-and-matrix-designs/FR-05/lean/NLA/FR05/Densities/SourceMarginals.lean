/-
Marginal identities for the source planted coordinate law.

These transport the radial estimate from `RadialTail.lean` to the actual
independent-coordinate measure used for one row in (3.18).
-/
import NLA.FR05.Densities.RadialTail

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace NLA.FR05

/-- The radial coordinate is the first marginal of the scalar law. -/
theorem sourceScalarLaw_radial_marginal
    {η δ ε : ℝ} (hε : 0 < ε) :
    Measure.map (fun p : SourcePlantedScalars => p.1) (sourceScalarLaw η δ ε) =
      sourceRadialLaw η δ := by
  let : IsProbabilityMeasure (sourceUniformInterval (-ε) ε) :=
    isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  unfold sourceScalarLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The radial coordinate remains the first marginal after adjoining the
independent complex-Gaussian tail. -/
theorem sourceCoordinateLaw_radial_marginal
    {η δ ε : ℝ} (n : ℕ) (hε : 0 < ε) :
    Measure.map (fun p : SourcePlantedCoordinates n => p.1.1)
      (sourceCoordinateLaw η δ ε n) = sourceRadialLaw η δ := by
  change Measure.map ((fun p : SourcePlantedScalars => p.1) ∘ Prod.fst)
    (sourceCoordinateLaw η δ ε n) = sourceRadialLaw η δ
  rw [← Measure.map_map measurable_fst measurable_fst]
  unfold sourceCoordinateLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact sourceScalarLaw_radial_marginal hε

/-- A radial upper-ray event under one source coordinate sample has exactly
the radial-law probability. -/
theorem sourceCoordinateLaw_radial_tail
    {η δ ε t : ℝ} (n : ℕ) (hε : 0 < ε) :
    sourceCoordinateLaw η δ ε n {p | t ≤ p.1.1} =
      sourceRadialLaw η δ (Ici t) := by
  have hmap := sourceCoordinateLaw_radial_marginal (η := η) (δ := δ) n hε
  rw [← hmap]
  have hmeas : Measurable (fun p : SourcePlantedCoordinates n => p.1.1) :=
    measurable_fst.comp measurable_fst
  rw [Measure.map_apply hmeas measurableSet_Ici]
  rfl

/-- The radial tail bound at the Proposition 3.1 scale applies to every
individual source-coordinate row. -/
theorem sourceCoordinateLaw_sourceM_radial_tail
    {M : ℕ} (n : ℕ) (hM : 1 ≤ M) :
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        {p | 8 * (M : ℝ) ≤ p.1.1} ≤
      (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
  rw [sourceCoordinateLaw_radial_tail n (sourceEpsilon_pos M hM)]
  exact sourceRadialLaw_sourceM_apply_Ici_le hM

/-- The squared Euclidean energy is a measurable function of a finite
complex tail vector. -/
theorem measurable_signalEnergy {n : ℕ} :
    Measurable (signalEnergy (n := n)) := by
  unfold signalEnergy squaredEuclideanNorm
  fun_prop

/-- The source complex-Gaussian tail law satisfies the checked source-scale
energy estimate. -/
theorem standardComplexGaussianTail_energy_tail (n : ℕ) :
    standardComplexGaussianTail n {w | 8 * (n : ℝ) ≤ signalEnergy w} ≤
      ENNReal.ofReal (Real.exp (-3 * (n : ℝ))) := by
  unfold standardComplexGaussianTail
  rw [Measure.map_apply measurable_standardComplexGaussianTail_map]
  · apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    change (Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)).real
      {x | 8 * (n : ℝ) ≤ signalEnergy (standardComplexTail x)} ≤
        (ENNReal.ofReal (Real.exp (-3 * (n : ℝ)))).toReal
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact tail_standardComplexTail_eight_mul n
  · exact measurableSet_Ici.preimage measurable_signalEnergy

/-- The independent complex-Gaussian tail is the second marginal of one
source-coordinate row. -/
theorem sourceCoordinateLaw_tail_marginal
    {η δ ε : ℝ} (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    Measure.map (fun p : SourcePlantedCoordinates n => p.2)
      (sourceCoordinateLaw η δ ε n) = standardComplexGaussianTail n := by
  let : IsProbabilityMeasure (sourceScalarLaw η δ ε) :=
    isProbabilityMeasure_sourceScalarLaw hη0 hη1 hε
  unfold sourceCoordinateLaw
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The complex-Gaussian energy tail applies directly to the tail coordinate
of one actual source-coordinate row. -/
theorem sourceCoordinateLaw_tail_energy_tail
    {η δ ε : ℝ} (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    sourceCoordinateLaw η δ ε n {p | 8 * (n : ℝ) ≤ signalEnergy p.2} ≤
      ENNReal.ofReal (Real.exp (-3 * (n : ℝ))) := by
  let s : Set (Signal n) := {w | 8 * (n : ℝ) ≤ signalEnergy w}
  have hs : MeasurableSet s := measurableSet_Ici.preimage measurable_signalEnergy
  have hmap := sourceCoordinateLaw_tail_marginal (η := η) (δ := δ) n hη0 hη1 hε
  calc
    sourceCoordinateLaw η δ ε n {p | 8 * (n : ℝ) ≤ signalEnergy p.2} =
        (Measure.map (fun p : SourcePlantedCoordinates n => p.2)
          (sourceCoordinateLaw η δ ε n)) s := by
      rw [Measure.map_apply measurable_snd hs]
      rfl
    _ = standardComplexGaussianTail n s := by rw [hmap]
    _ ≤ ENNReal.ofReal (Real.exp (-3 * (n : ℝ))) := by
      exact standardComplexGaussianTail_energy_tail n

end NLA.FR05
