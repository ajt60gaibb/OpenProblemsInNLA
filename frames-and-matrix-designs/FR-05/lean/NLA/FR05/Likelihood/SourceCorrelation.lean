import NLA.FR05.Gaussian.GaussianFrameRows
import NLA.FR05.Likelihood.HaarLikelihood

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NLA.FR05

inductive SourceDensityKind
  | planted
  | reference

def sourceDensity (a : SourceDensityKind) (M : ℕ) : (Fin 2 → ℂ) → ℝ :=
  match a with
  | .planted => sourcePlantedDensity M
  | .reference => sourceReferenceDensity M

def sourceDensityBound (M : ℕ) : ℝ := Real.exp 1 * (M : ℝ) ^ 52 + 4

theorem sourceDensityBound_nonneg (M : ℕ) : 0 ≤ sourceDensityBound M := by
  unfold sourceDensityBound
  positivity

theorem measurable_sourceDensity (a : SourceDensityKind) (M : ℕ) :
    Measurable (sourceDensity a M) := by
  cases a with
  | planted => exact measurable_sourcePlantedDensity M
  | reference => exact measurable_sourceReferenceDensity M

theorem sourceDensity_nonneg (a : SourceDensityKind) (M : ℕ) (z : Fin 2 → ℂ) :
    0 ≤ sourceDensity a M z := by
  cases a with
  | planted => exact sourcePlantedDensity_nonneg M z
  | reference => exact (sourceReferenceDensity_pos M z).le

theorem sourceDensity_le {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind)
    (z : Fin 2 → ℂ) : sourceDensity a M z ≤ sourceDensityBound M := by
  unfold sourceDensityBound
  cases a with
  | planted =>
    exact (sourcePlantedDensity_le (by lia) z).trans (by linarith)
  | reference =>
    exact (sourceReferenceDensity_le_four hM z).trans (le_add_of_nonneg_left (by positivity))

/-- One Gaussian row shared by two Haar frames, before passing to their overlap. -/
def sourcePairKernel {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (U V : SourceUnitary M) : ℝ :=
  ∫ x, sourceDensity a M (sourceProjectedRow hM U x) *
    sourceDensity b M (sourceProjectedRow hM V x) ∂standardComplexGaussianTail M

theorem measurable_sourcePairKernel {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    Measurable (fun p : SourceUnitary M × SourceUnitary M ↦
      sourcePairKernel hM a b p.1 p.2) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  exact ((measurable_sourceDensity a M).comp
    ((continuous_sourceProjectedRow hM).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).mul
    ((measurable_sourceDensity b M).comp
      ((continuous_sourceProjectedRow hM).measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

theorem sourcePairKernel_nonneg {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (U V : SourceUnitary M) : 0 ≤ sourcePairKernel hM a b U V :=
  integral_nonneg (fun _ ↦ mul_nonneg
    (sourceDensity_nonneg a M _) (sourceDensity_nonneg b M _))

theorem sourcePairKernel_le {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (U V : SourceUnitary M) :
    sourcePairKernel hM a b U V ≤ sourceDensityBound M ^ 2 := by
  have hf : Measurable (fun x ↦ sourceDensity a M (sourceProjectedRow hM U x) *
      sourceDensity b M (sourceProjectedRow hM V x)) :=
    ((measurable_sourceDensity a M).comp
      ((continuous_sourceProjectedRow hM).measurable.comp
        (measurable_const.prodMk measurable_id))).mul
    ((measurable_sourceDensity b M).comp
      ((continuous_sourceProjectedRow hM).measurable.comp
        (measurable_const.prodMk measurable_id)))
  have hb : ∀ x, 0 ≤ sourceDensity a M (sourceProjectedRow hM U x) *
      sourceDensity b M (sourceProjectedRow hM V x) ∧
      sourceDensity a M (sourceProjectedRow hM U x) *
        sourceDensity b M (sourceProjectedRow hM V x) ≤ sourceDensityBound M ^ 2 := by
    intro x
    constructor
    · exact mul_nonneg (sourceDensity_nonneg a M _) (sourceDensity_nonneg b M _)
    · simpa only [pow_two] using mul_le_mul
        (sourceDensity_le hM a _) (sourceDensity_le hM b _)
        (sourceDensity_nonneg b M _) (sourceDensityBound_nonneg M)
  have hi : Integrable (fun x ↦ sourceDensity a M (sourceProjectedRow hM U x) *
      sourceDensity b M (sourceProjectedRow hM V x)) (standardComplexGaussianTail M) := by
    apply Integrable.of_bound hf.aestronglyMeasurable (sourceDensityBound M ^ 2)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (hb x).2
  unfold sourcePairKernel
  calc
    _ ≤ ∫ _, sourceDensityBound M ^ 2 ∂standardComplexGaussianTail M :=
      integral_mono hi (integrable_const _) (fun x ↦ (hb x).2)
    _ = _ := by simp

theorem integrable_sourcePairKernel_pow {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (N : ℕ) :
    Integrable (fun p : SourceUnitary M × SourceUnitary M ↦
      sourcePairKernel hM a b p.1 p.2 ^ N)
      ((sourceUnitaryLaw M).prod (sourceUnitaryLaw M)) := by
  apply Integrable.of_bound
    ((measurable_sourcePairKernel hM a b).pow_const N).aestronglyMeasurable
    ((sourceDensityBound M ^ 2) ^ N)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sourcePairKernel_nonneg hM a b _ _) N)]
  exact pow_le_pow_left₀ (sourcePairKernel_nonneg hM a b _ _)
    (sourcePairKernel_le hM a b _ _) N

/-- The source second-moment identity (3.17) in Haar pair coordinates. -/
theorem source_second_moment_eq_pair_kernel {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) :
    (∫ A, sourceLikelihood hM (sourceDensity a M) A *
      sourceLikelihood hM (sourceDensity b M) A
      ∂standardComplexGaussianFrame (sourceRowCount M) M) =
    ∫ p : SourceUnitary M × SourceUnitary M,
      sourcePairKernel hM a b p.1 p.2 ^ sourceRowCount M
      ∂(sourceUnitaryLaw M).prod (sourceUnitaryLaw M) := by
  rw [standardComplexGaussianFrame_eq_pi]
  exact iid_mixture_second_moment (sourceUnitaryLaw M) (standardComplexGaussianTail M)
    (fun U x ↦ sourceDensity a M (sourceProjectedRow hM U x))
    (fun U x ↦ sourceDensity b M (sourceProjectedRow hM U x))
    ((measurable_sourceDensity a M).comp (continuous_sourceProjectedRow hM).measurable)
    ((measurable_sourceDensity b M).comp (continuous_sourceProjectedRow hM).measurable)
    (sourceDensityBound_nonneg M) (sourceDensityBound_nonneg M)
    (fun _ _ ↦ ⟨sourceDensity_nonneg a M _, sourceDensity_le hM a _⟩)
    (fun _ _ ↦ ⟨sourceDensity_nonneg b M _, sourceDensity_le hM b _⟩)
    (sourceRowCount M)

/-- The exact integrand to be bounded in Proposition 3.2. -/
theorem sourceLikelihoodL2_eq_pair_integral (M : ℕ) (hM : 2 ≤ M) :
    sourceLikelihoodL2 M hM =
      ∫ p : SourceUnitary M × SourceUnitary M,
        (sourcePairKernel hM .planted .planted p.1 p.2 ^ sourceRowCount M +
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M) -
          2 * sourcePairKernel hM .planted .reference p.1 p.2 ^ sourceRowCount M
        ∂(sourceUnitaryLaw M).prod (sourceUnitaryLaw M) := by
  have hgg := integrable_sourcePairKernel_pow hM .planted .planted (sourceRowCount M)
  have hrr := integrable_sourcePairKernel_pow hM .reference .reference (sourceRowCount M)
  have hgr := integrable_sourcePairKernel_pow hM .planted .reference (sourceRowCount M)
  have hsub := integral_sub (hgg.add hrr) (hgr.const_mul (2 : ℝ))
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hgg hrr, integral_const_mul]
  rw [← source_second_moment_eq_pair_kernel hM .planted .planted,
    ← source_second_moment_eq_pair_kernel hM .reference .reference,
    ← source_second_moment_eq_pair_kernel hM .planted .reference]
  exact sourceLikelihoodL2_identity M hM

/-- No pointwise sign of the combined kernel integrand is needed. -/
theorem sourceLikelihoodL2_le_pair_differences (M : ℕ) (hM : 2 ≤ M) :
    sourceLikelihoodL2 M hM ≤
      (∫ p : SourceUnitary M × SourceUnitary M,
        |sourcePairKernel hM .planted .planted p.1 p.2 ^ sourceRowCount M -
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M|
        ∂(sourceUnitaryLaw M).prod (sourceUnitaryLaw M)) +
      2 * (∫ p : SourceUnitary M × SourceUnitary M,
        |sourcePairKernel hM .planted .reference p.1 p.2 ^ sourceRowCount M -
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M|
        ∂(sourceUnitaryLaw M).prod (sourceUnitaryLaw M)) := by
  have hgg := integrable_sourcePairKernel_pow hM .planted .planted (sourceRowCount M)
  have hrr := integrable_sourcePairKernel_pow hM .reference .reference (sourceRowCount M)
  have hgr := integrable_sourcePairKernel_pow hM .planted .reference (sourceRowCount M)
  rw [sourceLikelihoodL2_eq_pair_integral]
  calc
    _ ≤ ∫ p : SourceUnitary M × SourceUnitary M,
        |sourcePairKernel hM .planted .planted p.1 p.2 ^ sourceRowCount M -
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M| +
        2 * |sourcePairKernel hM .planted .reference p.1 p.2 ^ sourceRowCount M -
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M|
        ∂(sourceUnitaryLaw M).prod (sourceUnitaryLaw M) := by
      apply integral_mono ((hgg.add hrr).sub (hgr.const_mul (2 : ℝ)))
        ((hgg.sub hrr).abs.add ((hgr.sub hrr).abs.const_mul (2 : ℝ)))
      intro p
      have h₁ := le_abs_self
        (sourcePairKernel hM .planted .planted p.1 p.2 ^ sourceRowCount M -
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M)
      have h₂ := neg_le_abs
        (sourcePairKernel hM .planted .reference p.1 p.2 ^ sourceRowCount M -
          sourcePairKernel hM .reference .reference p.1 p.2 ^ sourceRowCount M)
      dsimp only [Pi.add_apply, Pi.sub_apply]
      linarith
    _ = _ := by
      have hadd := integral_add (hgg.sub hrr).abs ((hgr.sub hrr).abs.const_mul (2 : ℝ))
      simp only [Pi.sub_apply] at hadd
      rw [hadd, integral_const_mul]

end NLA.FR05
