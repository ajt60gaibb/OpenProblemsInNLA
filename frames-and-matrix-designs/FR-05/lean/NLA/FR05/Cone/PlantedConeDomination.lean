import NLA.FR05.Cone.PlantedConeParameters
import NLA.FR05.Likelihood.CanonicalKernelBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Real Set
open scoped ENNReal

namespace NLA.FR05

def plantedConeNormalizer (M : ℕ) : ℝ :=
  (2 * sourceEpsilon M * sourceRadialNormalizer M)⁻¹

theorem plantedConeNormalizer_nonneg {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ plantedConeNormalizer M :=
  inv_nonneg.mpr (mul_nonneg (mul_nonneg (by norm_num) (sourceEpsilon_pos M hM).le)
    (sourceRadialNormalizer_pos M).le)

theorem plantedRadiusDensity_ratio (M : ℕ) (s : ℝ) :
    plantedRadiusDensity M s / (2 * sourceEpsilon M) =
      plantedConeNormalizer M * coneRadiusDensity s := by
  unfold plantedRadiusDensity plantedConeNormalizer coneRadiusDensity
  ring

theorem lintegral_sourcePlanted_le_cones {M : ℕ} (hM : 1 ≤ M)
    (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂sourceDensityLaw .planted M) ≤
      ENNReal.ofReal (plantedConeNormalizer M) *
        ∫⁻ t in Icc (-sourceEpsilon M) (sourceEpsilon M), ∫⁻ z, f z ∂coneMeasure t := by
  rw [lintegral_sourcePlantedDensityLaw_parameters hM f hf]
  simp_rw [plantedRadiusDensity_ratio,
    ENNReal.ofReal_mul (plantedConeNormalizer_nonneg hM), mul_assoc]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    unfold coneRadiusDensity
    fun_prop)]
  simp_rw [lintegral_const_mul' (ENNReal.ofReal (plantedConeNormalizer M)) _ ENNReal.ofReal_ne_top]
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro t
  dsimp only
  rw [lintegral_coneMeasure_parameters t f hf]
  apply lintegral_mono_set
  intro s hs
  exact (sourceDelta_pos M hM).le.trans hs

theorem lintegral_planted_pair_le_cones {M : ℕ} (hM : 2 ≤ M)
    (R : Signal 2 × Signal 2 → ℝ≥0∞) (hR : Measurable R) :
    (∫⁻ p, R p ∂(sourceDensityLaw .planted M).prod (sourceDensityLaw .planted M)) ≤
      ENNReal.ofReal (plantedConeNormalizer M)^2 *
        ∫⁻ t in Icc (-sourceEpsilon M) (sourceEpsilon M),
          ∫⁻ s in Icc (-sourceEpsilon M) (sourceEpsilon M),
            ∫⁻ p, R p ∂(coneMeasure t).prod (coneMeasure s) := by
  let : IsProbabilityMeasure (sourceDensityLaw .planted M) := isProbabilityMeasure_sourceDensityLaw hM _
  have hM1 : 1 ≤ M := by lia
  rw [lintegral_prod _ hR.aemeasurable]
  apply (lintegral_sourcePlanted_le_cones hM1
    (fun z ↦ ∫⁻ w, R (z, w) ∂sourceDensityLaw .planted M)
    (by apply Measurable.lintegral_prod_right; exact hR)).trans
  have hinner (t : ℝ) :
      (∫⁻ z, ∫⁻ w, R (z, w) ∂sourceDensityLaw .planted M ∂coneMeasure t) ≤
      ENNReal.ofReal (plantedConeNormalizer M) *
        ∫⁻ s in Icc (-sourceEpsilon M) (sourceEpsilon M),
          ∫⁻ p, R p ∂(coneMeasure t).prod (coneMeasure s) := by
    calc
      _ ≤ ∫⁻ z, (ENNReal.ofReal (plantedConeNormalizer M) *
          ∫⁻ s in Icc (-sourceEpsilon M) (sourceEpsilon M),
            ∫⁻ w, R (z, w) ∂coneMeasure s) ∂coneMeasure t :=
        lintegral_mono fun z ↦ lintegral_sourcePlanted_le_cones hM1 _ (by fun_prop)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        have hm : Measurable (fun p : Signal 2 × ℝ ↦ ∫⁻ w, R (p.1, w) ∂coneMeasure p.2) := by
          have he (p : Signal 2 × ℝ) :
              (∫⁻ w, R (p.1, w) ∂coneMeasure p.2) =
                ∫⁻ q, R (p.1, conePoint p.2 q)
                  ∂AddCircle.haarAddCircle.prod coneScalarMeasure := by
            exact lintegral_map (by fun_prop) (continuous_conePoint p.2).measurable
          simp_rw [he]
          apply Measurable.lintegral_prod_right
          unfold conePoint coneBasis
          fun_prop
        rw [lintegral_lintegral_swap hm.aemeasurable]
        apply lintegral_congr
        intro s
        exact (lintegral_prod R hR.aemeasurable).symm
  calc
    _ ≤ ENNReal.ofReal (plantedConeNormalizer M) *
        ∫⁻ t in Icc (-sourceEpsilon M) (sourceEpsilon M),
          ENNReal.ofReal (plantedConeNormalizer M) *
            ∫⁻ s in Icc (-sourceEpsilon M) (sourceEpsilon M),
              ∫⁻ p, R p ∂(coneMeasure t).prod (coneMeasure s) :=
      mul_le_mul' le_rfl (lintegral_mono hinner)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, pow_two, mul_assoc]

end NLA.FR05
