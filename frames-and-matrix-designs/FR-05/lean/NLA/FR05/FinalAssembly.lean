/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The unconditional FR-05 bound and vanishing-probability theorem, assembled
from the proved sampler identities and Propositions 3.1 and 3.2.
-/
import NLA.FR05.Bridges.SourceReferenceLawBridge
import NLA.FR05.LikelihoodComparison
import NLA.FR05.Asymptotics

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace NLA.FR05

@[fun_prop] theorem measurable_sourceFrameAtDimension {M : ℕ} (hM : 2 ≤ M) :
    Measurable (sourceFrameAtDimension hM) := by
  unfold sourceFrameAtDimension
  fun_prop

theorem phaseRetrievalInjective_sourceFrameAtDimension {M : ℕ} (hM : 2 ≤ M)
    (A : Frame (sourceRowCount M) (sourceTailDimension M + 2)) :
    PhaseRetrievalInjective (sourceFrameAtDimension hM A) ↔ PhaseRetrievalInjective A := by
  have transport (m n d : ℕ) (hd : n + 2 = d) (B : Frame m (n + 2)) :
      PhaseRetrievalInjective (fun i j ↦ B i (Fin.cast hd.symm j)) ↔
        PhaseRetrievalInjective B := by
    subst d
    rfl
  exact transport _ _ _ (sourceTailDimension_add_two hM) A

/-- The literal planted likelihood assigns the injectivity event exactly the
probability bounded in Proposition 3.1, including the dimension relabelling. -/
theorem sourcePlantedLikelihood_injective_probability {M : ℕ} (hM : 2 ≤ M) :
    ((standardComplexGaussianFrame (sourceRowCount M) M).withDensity
      (fun A ↦ ENNReal.ofReal (sourcePlantedLikelihood hM A))).real
        {A | PhaseRetrievalInjective A} =
      (sourceHaarPlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} := by
  have he : sourceFrameAtDimension hM ⁻¹' {A | PhaseRetrievalInjective A} =
      {A | PhaseRetrievalInjective A} := by
    ext A
    exact phaseRetrievalInjective_sourceFrameAtDimension hM A
  rw [← sourceHaarPlantedFrameLawAt_eq_likelihood hM, Measure.real_def,
    Measure.map_apply (measurable_sourceFrameAtDimension hM)
      (show MeasurableSet {A : Frame (sourceRowCount M) M | PhaseRetrievalInjective A}
        from measurableSet_phaseRetrievalInjective _ _), he]
  rfl

theorem integral_sourcePlantedLikelihood_injective {M : ℕ} (hM : 2 ≤ M) :
    (∫ A in {A | PhaseRetrievalInjective A}, sourcePlantedLikelihood hM A
      ∂standardComplexGaussianFrame (sourceRowCount M) M) =
      (sourceHaarPlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} := by
  rw [← sourcePlantedLikelihood_injective_probability hM, Measure.real_def,
    withDensity_apply _ (show MeasurableSet
      {A : Frame (sourceRowCount M) M | PhaseRetrievalInjective A} from
        measurableSet_phaseRetrievalInjective _ _)]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (sourcePlantedLikelihood_nonneg hM))
    (measurable_sourcePlantedLikelihood hM).aestronglyMeasurable

theorem memLp_sourcePlantedLikelihood {M : ℕ} (hM : 2 ≤ M) :
    MemLp (sourcePlantedLikelihood hM) 2 (standardComplexGaussianFrame (sourceRowCount M) M) := by
  apply MemLp.of_bound (measurable_sourcePlantedLikelihood hM).aestronglyMeasurable
    ((Real.exp 1 * (M : ℝ) ^ 52) ^ sourceRowCount M)
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (sourcePlantedLikelihood_nonneg hM A)]
  exact sourcePlantedLikelihood_le hM A

theorem memLp_sourceReferenceLikelihood {M : ℕ} (hM : 2 ≤ M) :
    MemLp (sourceReferenceLikelihood hM) 2 (standardComplexGaussianFrame (sourceRowCount M) M) := by
  apply MemLp.of_bound (measurable_sourceReferenceLikelihood hM).aestronglyMeasurable
    (4 ^ sourceRowCount M)
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceReferenceLikelihood_nonneg hM A)]
  exact sourceReferenceLikelihood_le hM A

/-- The source's Cauchy--Schwarz step for the original Gaussian injectivity
event, with no comparison hypothesis left unproved. -/
theorem phaseRetrieval_probability_le_planted_add_sqrt {M : ℕ} (hM : 2 ≤ M) :
    phaseRetrievalProbability M ≤
      (sourceHaarPlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} +
        Real.sqrt (sourceLikelihoodL2 M hM * phaseRetrievalProbability M) := by
  have hg := memLp_sourcePlantedLikelihood hM
  have hr := memLp_sourceReferenceLikelihood hM
  have hcs := abs_setIntegral_le_sqrt_integral_sq (hg.sub hr)
    {A | PhaseRetrievalInjective A}
  simp only [Pi.sub_apply] at hcs
  rw [integral_sub (hg.integrable (by norm_num)).integrableOn
      (hr.integrable (by norm_num)).integrableOn,
    integral_sourcePlantedLikelihood_injective hM,
    integral_sourceReferenceLikelihood_injective hM] at hcs
  change |(sourceHaarPlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} -
      phaseRetrievalProbability M| ≤
    Real.sqrt (sourceLikelihoodL2 M hM * phaseRetrievalProbability M) at hcs
  linarith [neg_le_abs ((sourceHaarPlantedFrameLawAt M).real
    {A | PhaseRetrievalInjective A} - phaseRetrievalProbability M)]

/-- Combining Propositions 3.1 and 3.2 supplies the eventual comparison
required by the source-independent numerical reduction. -/
theorem source_eventual_probability_comparison :
    ∃ (D : ℕ) (a b : ℝ), 2 ≤ D ∧ 0 < a ∧ 0 < b ∧ ∀ M : ℕ, D ≤ M →
      phaseRetrievalProbability M ≤ a / (M : ℝ) ^ 2 +
        Real.sqrt (b * phaseRetrievalProbability M / M) := by
  obtain ⟨a, ha, D₁, hD₁, hplant⟩ := proposition_3_1_haar
  obtain ⟨b, hb, D₂, hD₂, hL2⟩ := proposition_3_2
  refine ⟨max D₁ D₂, a, b, hD₁.trans (le_max_left _ _), ha, hb, ?_⟩
  intro M hM
  have h₁ : D₁ ≤ M := (le_max_left _ _).trans hM
  have h₂ : D₂ ≤ M := (le_max_right _ _).trans hM
  have hdim : 2 ≤ M := hD₁.trans h₁
  calc
    _ ≤ (sourceHaarPlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} +
        Real.sqrt (sourceLikelihoodL2 M hdim * phaseRetrievalProbability M) :=
      phaseRetrieval_probability_le_planted_add_sqrt hdim
    _ ≤ a / (M : ℝ) ^ 2 + Real.sqrt ((b / M) * phaseRetrievalProbability M) :=
      add_le_add (hplant M h₁) (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_right (hL2 M hdim h₂) (phaseRetrievalProbability_nonneg M)))
    _ = _ := by congr 2; ring

/-- Theorem 1.4: the exact quantitative strengthening of the original FR-05 target. -/
theorem phaseRetrieval_injective_probability_le_inv_proved :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → phaseRetrievalProbability d ≤ C / d := by
  obtain ⟨D, a, b, hD, ha, hb, hc⟩ := source_eventual_probability_comparison
  exact phaseRetrieval_injective_probability_le_inv_of_source_comparison
    D a b (by lia) ha.le hb.le hc

/-- The original FR-05 limit, for iid standard complex-Gaussian frames
with `4d - 5` rows and the original all-signals injectivity predicate. -/
theorem phaseRetrieval_injective_probability_tendsto_zero_proved :
    Tendsto phaseRetrievalProbability atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := phaseRetrieval_injective_probability_le_inv_proved
  exact squeeze_zero'
    (Filter.Eventually.of_forall phaseRetrievalProbability_nonneg)
    (Filter.eventually_atTop.2 ⟨2, hC⟩) (tendsto_const_div_atTop_nhds_zero_nat C)

end NLA.FR05
