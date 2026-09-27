import NLA.FR05.Densities.SourcePlantedRadial
import NLA.FR05.Likelihood.SourceCorrelation

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLA.FR05

def sourceDensityLaw (a : SourceDensityKind) (M : ℕ) : Measure (Signal 2) :=
  (standardComplexGaussianTail 2).withDensity (fun z ↦ ENNReal.ofReal (sourceDensity a M z))

theorem isProbabilityMeasure_sourceDensityLaw {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind) :
    IsProbabilityMeasure (sourceDensityLaw a M) := by
  cases a with
  | planted => exact isProbabilityMeasure_sourcePlantedDensityLaw (by lia)
  | reference => exact isProbabilityMeasure_sourceReferenceLaw M

theorem sourceDensityLaw_integrable_radius {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind) :
    Integrable sourceRadiusSq (sourceDensityLaw a M) := by
  cases a with
  | planted => exact sourcePlantedDensityLaw_integrable_radius (by lia)
  | reference => exact sourceReferenceLaw_integrable_radius M

theorem sourceDensityLaw_map_coordinatePhase (a : SourceDensityKind) (M : ℕ)
    (c : Fin 2 → ℂ) (hc : ∀ j, Complex.normSq (c j) = 1) :
    (sourceDensityLaw a M).map (coordinatePhase c) = sourceDensityLaw a M := by
  cases a with
  | planted => exact sourcePlantedDensityLaw_map_coordinatePhase M c hc
  | reference => exact sourceReferenceLaw_map_coordinatePhase M c hc

theorem sourceDensityLaw_map_swapTwo (a : SourceDensityKind) (M : ℕ) :
    (sourceDensityLaw a M).map swapTwo = sourceDensityLaw a M := by
  cases a with
  | planted => exact sourcePlantedDensityLaw_map_swapTwo M
  | reference => exact sourceReferenceLaw_map_swapTwo M

theorem integral_sourceDensityLaw_complex (a : SourceDensityKind) (M : ℕ)
    (f : Signal 2 → ℂ) :
    (∫ z, f z ∂sourceDensityLaw a M) =
      ∫ z, (sourceDensity a M z : ℂ) * f z ∂standardComplexGaussianTail 2 := by
  rw [sourceDensityLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_sourceDensity a M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceDensity_nonneg a M _), Complex.real_smul]

theorem integrable_sourceDensityLaw_complex_iff (a : SourceDensityKind) (M : ℕ)
    (f : Signal 2 → ℂ) :
    Integrable f (sourceDensityLaw a M) ↔
      Integrable (fun z ↦ (sourceDensity a M z : ℂ) * f z)
        (standardComplexGaussianTail 2) := by
  rw [sourceDensityLaw, integrable_withDensity_iff_integrable_smul'
    (measurable_sourceDensity a M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceDensity_nonneg a M _), Complex.real_smul]

theorem integral_sourceDensity {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind) :
    (∫ z, sourceDensity a M z ∂standardComplexGaussianTail 2) = 1 := by
  cases a with
  | planted => exact integral_sourcePlantedDensity (by lia)
  | reference => exact integral_sourceReferenceDensity M

theorem integrable_sourceDensity_coordinate {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (i : Fin 2) :
    Integrable (fun z ↦ (sourceDensity a M z : ℂ) * z i)
      (standardComplexGaussianTail 2) := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  exact (integrable_sourceDensityLaw_complex_iff a M _).mp
    (integrable_coordinate (sourceDensityLaw_integrable_radius hM a) i)

theorem integrable_sourceDensity_coordinate_product {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (i j : Fin 2) :
    Integrable (fun z ↦ (sourceDensity a M z : ℂ) * (z i * z j))
      (standardComplexGaussianTail 2) :=
  (integrable_sourceDensityLaw_complex_iff a M _).mp
    (integrable_coordinate_product (sourceDensityLaw_integrable_radius hM a) i j)

theorem integrable_sourceDensity_coordinate_conj_product {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (i j : Fin 2) :
    Integrable (fun z ↦ (sourceDensity a M z : ℂ) * (z i * star (z j)))
      (standardComplexGaussianTail 2) :=
  (integrable_sourceDensityLaw_complex_iff a M _).mp
    (integrable_coordinate_conj_product (sourceDensityLaw_integrable_radius hM a) i j)

theorem integral_sourceDensity_coordinate (a : SourceDensityKind) (M : ℕ) (i : Fin 2) :
    (∫ z, (sourceDensity a M z : ℂ) * z i ∂standardComplexGaussianTail 2) = 0 := by
  rw [← integral_sourceDensityLaw_complex]
  exact integral_coordinate_eq_zero_of_phase (sourceDensityLaw_map_coordinatePhase a M) i

theorem integral_sourceDensity_coordinate_product (a : SourceDensityKind) (M : ℕ)
    (i j : Fin 2) :
    (∫ z, (sourceDensity a M z : ℂ) * (z i * z j) ∂standardComplexGaussianTail 2) = 0 := by
  rw [← integral_sourceDensityLaw_complex]
  exact integral_coordinate_product_eq_zero_of_phase
    (sourceDensityLaw_map_coordinatePhase a M) i j

theorem integral_sourceDensity_coordinate_conj_product {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (i j : Fin 2) :
    (∫ z, (sourceDensity a M z : ℂ) * (z i * star (z j)) ∂standardComplexGaussianTail 2) =
      if i = j then (sourceVariance M : ℂ) else 0 := by
  rw [← integral_sourceDensityLaw_complex]
  cases a with
  | planted => exact sourcePlantedDensityLaw_covariance (by lia) i j
  | reference => exact sourceReferenceLaw_covariance M i j

theorem integrable_sourceDensity_exp_quarter {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) :
    Integrable (fun z ↦ sourceDensity a M z * Real.exp (sourceRadiusSq z / 4))
      (standardComplexGaussianTail 2) := by
  have he (z : Signal 2) : sourceRadiusSq z / 4 = (1 / 4) * sourceRadiusSq z := by ring
  simp_rw [he]
  cases a with
  | planted => exact integrable_sourcePlantedDensity_mul_exp (by lia) (by norm_num)
  | reference =>
    apply integrable_sourceReferenceDensity_mul_exp
    have h := (one_le_inv₀ (sourceVariance_pos M)).mpr (sourceVariance_le_one hM)
    linarith

theorem sourceDensity_exp_quarter_bound {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) :
    (∫ z, sourceDensity a M z * Real.exp (sourceRadiusSq z / 4)
      ∂standardComplexGaussianTail 2) ≤ 4 * Real.exp 1 := by
  cases a with
  | planted => exact sourcePlantedDensity_exp_quarter_bound (by lia)
  | reference =>
    apply (sourceReferenceDensity_exp_quarter_bound hM).trans
    have h : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith

end NLA.FR05
