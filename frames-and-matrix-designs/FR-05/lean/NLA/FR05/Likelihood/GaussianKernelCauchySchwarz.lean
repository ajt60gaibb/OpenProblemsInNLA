import NLA.FR05.Likelihood.GaussianConditionalPair
import NLA.FR05.Overlap.Spectrum

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real Matrix
open scoped ENNReal

namespace NLA.FR05

attribute [local fun_prop] measurable_sourceDensity

def gaussianSmoothedDensity (a : SourceDensityKind) (M : ℕ)
    (L : Matrix (Fin 4) (Fin 2) ℂ) (N : SourceOverlapMatrix) (z : Signal 4) : ℝ :=
  ∫ x, sourceDensity a M (Lᴴ *ᵥ star z + Nᴴ *ᵥ star x) ∂standardComplexGaussianTail 2

@[fun_prop] theorem measurable_gaussianSmoothedDensity (a : SourceDensityKind) (M : ℕ)
    (L : Matrix (Fin 4) (Fin 2) ℂ) (N : SourceOverlapMatrix) :
    Measurable (gaussianSmoothedDensity a M L N) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  unfold Function.uncurry
  fun_prop

theorem gaussianSmoothedDensity_nonneg (a : SourceDensityKind) (M : ℕ)
    (L : Matrix (Fin 4) (Fin 2) ℂ) (N : SourceOverlapMatrix) (z : Signal 4) :
    0 ≤ gaussianSmoothedDensity a M L N z :=
  integral_nonneg fun _ ↦ sourceDensity_nonneg a M _

theorem gaussianSmoothedDensity_le {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind)
    (L : Matrix (Fin 4) (Fin 2) ℂ) (N : SourceOverlapMatrix) (z : Signal 4) :
    gaussianSmoothedDensity a M L N z ≤ sourceDensityBound M := by
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x : Signal 2 ↦ sourceDensity_nonneg a M
      (Lᴴ *ᵥ star z + Nᴴ *ᵥ star x))
    (integrable_const (sourceDensityBound M) (μ := standardComplexGaussianTail 2))
    (Filter.Eventually.of_forall fun x ↦ sourceDensity_le hM a _)
  simpa [gaussianSmoothedDensity] using h

theorem memLp_gaussianSmoothedDensity {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind)
    (L : Matrix (Fin 4) (Fin 2) ℂ) (N : SourceOverlapMatrix) :
    MemLp (gaussianSmoothedDensity a M L N) 2 (standardComplexGaussianTail 4) := by
  apply MemLp.of_bound (measurable_gaussianSmoothedDensity a M L N).aestronglyMeasurable
    (sourceDensityBound M)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianSmoothedDensity_nonneg a M L N z)]
  exact gaussianSmoothedDensity_le hM a L N z

theorem integrable_sourceDensity_product_comp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    {f g : α → Signal 2} (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun x ↦ sourceDensity a M (f x) * sourceDensity b M (g x)) μ := by
  apply Integrable.of_bound (by apply Measurable.aestronglyMeasurable; fun_prop)
    (sourceDensityBound M ^ 2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sourceDensity_nonneg a M _) (sourceDensity_nonneg b M _))]
  simpa [pow_two] using mul_le_mul (sourceDensity_le hM a _) (sourceDensity_le hM b _)
    (sourceDensity_nonneg b M _) (sourceDensityBound_nonneg M)

theorem sourceDensityCorrelation_eq_smoothed {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (L R : Matrix (Fin 4) (Fin 2) ℂ) (N P : SourceOverlapMatrix)
    (hL : Lᴴ * L + Nᴴ * N = 1) (hR : Rᴴ * R + Pᴴ * P = 1)
    (hK : overlapOperatorNorm (Lᴴ * R) < 1) :
    sourceDensityCorrelation a b M (Lᴴ * R) =
      ∫ z, gaussianSmoothedDensity a M L N z * gaussianSmoothedDensity b M R P z
        ∂standardComplexGaussianTail 4 := by
  rw [sourceDensityCorrelation_eq_integral_canonical hK,
    ← conditionalGaussianLaw_eq_canonical L R N P hL hR hK,
    integral_map (continuous_conditionalGaussianMap L R N P).measurable.aemeasurable
      (by apply Measurable.aestronglyMeasurable; fun_prop)]
  rw [integral_prod _ (integrable_sourceDensity_product_comp hM a b
    (by unfold conditionalGaussianMap; fun_prop) (by unfold conditionalGaussianMap; fun_prop))]
  apply integral_congr_ae
  filter_upwards with z
  exact integral_prod_mul
    (fun x ↦ sourceDensity a M (Lᴴ *ᵥ star z + Nᴴ *ᵥ star x))
    (fun y ↦ sourceDensity b M (Rᴴ *ᵥ star z + Pᴴ *ᵥ star y))

theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ) * (∫ x, g x^2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hfn) (Filter.Eventually.of_forall hgn) (by simpa using hf)
    (by simpa using hg)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have hn : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg fun x ↦ mul_nonneg (hfn x) (hgn x)
  have hs := pow_le_pow_left₀ hn h 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg (f x)),
    Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg (g x))] at hs
  exact hs

theorem sourceDensityCorrelation_cauchy_schwarz {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation a b M K ^ 2 ≤
      sourceDensityCorrelation a a M (overlapLeftRoot K) *
        sourceDensityCorrelation b b M (overlapRightRoot K) := by
  obtain ⟨L, R, N, P, hLL, hRR, hLR, hL, hR⟩ := exists_overlap_latent_factors hK
  have hleft : overlapOperatorNorm (Lᴴ * L) < 1 := by rw [hLL, overlapLeftRoot_norm]; exact hK
  have hright : overlapOperatorNorm (Rᴴ * R) < 1 := by rw [hRR, overlapRightRoot_norm]; exact hK
  have hpair := sourceDensityCorrelation_eq_smoothed hM a b L R N P hL hR (by rwa [hLR])
  have hll := sourceDensityCorrelation_eq_smoothed hM a a L L N N hL hL hleft
  have hrr := sourceDensityCorrelation_eq_smoothed hM b b R R P P hR hR hright
  rw [hLR] at hpair
  rw [hLL] at hll
  rw [hRR] at hrr
  rw [hpair, hll, hrr]
  simpa only [← pow_two] using integral_mul_sq_le
    (memLp_gaussianSmoothedDensity hM a L N) (memLp_gaussianSmoothedDensity hM b R P)
    (gaussianSmoothedDensity_nonneg a M L N) (gaussianSmoothedDensity_nonneg b M R P)

end NLA.FR05
