import NLA.FR05.Gaussian.ComplexGaussianDensity
import NLA.FR05.Densities.SourceDensityMoments
import NLA.FR05.Likelihood.SourceOverlapKernel

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Matrix WithLp

namespace NLA.FR05

theorem sourceProjectedRow_law {M : ℕ} (hM : 2 ≤ M) (U : SourceUnitary M) :
    (standardComplexGaussianTail M).map (sourceProjectedRow hM U) =
      standardComplexGaussianTail 2 :=
  standardComplexGaussianTail_map_orthonormal _ (sourceTwoFrame_orthonormal hM U)

theorem integral_sourceProjectedDensity {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (U : SourceUnitary M) :
    (∫ x, sourceDensity a M (sourceProjectedRow hM U x)
      ∂standardComplexGaussianTail M) = 1 := by
  rw [← integral_map (φ := sourceProjectedRow hM U) (f := sourceDensity a M)
    ((continuous_sourceProjectedRow hM).comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable
    (measurable_sourceDensity a M).aestronglyMeasurable,
    sourceProjectedRow_law, integral_sourceDensity hM]

theorem integrable_sourceProjectedDensity {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (U : SourceUnitary M) :
    Integrable (fun x ↦ sourceDensity a M (sourceProjectedRow hM U x))
      (standardComplexGaussianTail M) := by
  by_contra hi
  have h := integral_sourceProjectedDensity hM a U
  rw [integral_undef hi] at h
  norm_num at h

theorem sourcePairKernel_le_densityBound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (U V : SourceUnitary M) :
    sourcePairKernel hM a b U V ≤ sourceDensityBound M := by
  have hi : Integrable (fun x ↦ sourceDensity a M (sourceProjectedRow hM U x) *
      sourceDensity b M (sourceProjectedRow hM V x)) (standardComplexGaussianTail M) := by
    apply Integrable.of_bound
      (by apply Measurable.aestronglyMeasurable
          exact ((measurable_sourceDensity a M).comp
            ((continuous_sourceProjectedRow hM).comp (continuous_const.prodMk continuous_id)).measurable).mul
            ((measurable_sourceDensity b M).comp
              ((continuous_sourceProjectedRow hM).comp (continuous_const.prodMk continuous_id)).measurable))
      (sourceDensityBound M ^ 2)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sourceDensity_nonneg a M _) (sourceDensity_nonneg b M _))]
    exact le_trans (mul_le_mul (sourceDensity_le hM a _) (sourceDensity_le hM b _)
      (sourceDensity_nonneg b M _) (sourceDensityBound_nonneg M)) (by rw [pow_two])
  unfold sourcePairKernel
  calc
    _ ≤ ∫ x, sourceDensityBound M * sourceDensity b M (sourceProjectedRow hM V x)
        ∂standardComplexGaussianTail M :=
      integral_mono hi ((integrable_sourceProjectedDensity hM b V).const_mul _)
        (fun x ↦ mul_le_mul_of_nonneg_right (sourceDensity_le hM a _) (sourceDensity_nonneg b M _))
    _ = _ := by rw [integral_const_mul, integral_sourceProjectedDensity hM, mul_one]

theorem sourceOverlapKernel_nonneg {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    0 ≤ sourceOverlapKernel hM a b K := by
  by_cases hK : K ∈ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2)
  · obtain ⟨⟨U, V⟩, rfl⟩ := hK
    rw [sourceOverlapKernel_apply]
    exact sourcePairKernel_nonneg hM a b U V
  · rw [sourceOverlapKernel_eq_zero hM a b K hK]

theorem sourceOverlapKernel_polynomial_bound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    sourceOverlapKernel hM a b K ≤ (Real.exp 1 + 4) * (M : ℝ) ^ 52 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by lia)
  have hp : (1 : ℝ) ≤ (M : ℝ) ^ 52 := one_le_pow₀ hM'
  have hc : sourceDensityBound M ≤ (Real.exp 1 + 4) * (M : ℝ) ^ 52 := by
    unfold sourceDensityBound
    nlinarith
  by_cases hK : K ∈ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2)
  · obtain ⟨⟨U, V⟩, rfl⟩ := hK
    rw [sourceOverlapKernel_apply]
    exact (sourcePairKernel_le_densityBound hM a b U V).trans hc
  · rw [sourceOverlapKernel_eq_zero hM a b K hK]
    positivity

end NLA.FR05
