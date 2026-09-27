import NLA.FR05.Densities.SourceLikelihood
import NLA.FR05.Probability
import Mathlib.Topology.Algebra.Star.Unitary
import NLA.FR05.Likelihood.LikelihoodAlgebra

/-!
# Haar likelihoods and second moments

The sections develop `HaarLikelihood`, `LikelihoodSecondMoment`, `SourceSecondMoments`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section HaarLikelihood

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

abbrev SourceUnitary (M : ℕ) := Matrix.unitaryGroup (Fin M) ℂ

instance sourceUnitaryCompactSpace (M : ℕ) : CompactSpace (SourceUnitary M) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Matrix (Fin M) (Fin M) ℂ) 1).of_isClosed_subset
    (isClosed_unitary (R := Matrix (Fin M) (Fin M) ℂ))
  intro U hU
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    entrywise_sup_norm_bound_of_unitary hU

instance sourceUnitarySecondCountableTopology (M : ℕ) :
    SecondCountableTopology (SourceUnitary M) := by
  let : SecondCountableTopology (Matrix (Fin M) (Fin M) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → ℂ))
  exact (Topology.IsInducing.subtypeVal
    (t := {U : Matrix (Fin M) (Fin M) ℂ | U ∈ Matrix.unitaryGroup (Fin M) ℂ})).secondCountableTopology

instance sourceUnitaryMeasurableSpace (M : ℕ) : MeasurableSpace (SourceUnitary M) :=
  borel (SourceUnitary M)

instance sourceUnitaryBorelSpace (M : ℕ) : BorelSpace (SourceUnitary M) := ⟨rfl⟩

/-- Normalized Haar measure on the complex unitary group. -/
def sourceUnitaryLaw (M : ℕ) : Measure (SourceUnitary M) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance (M : ℕ) : IsProbabilityMeasure (sourceUnitaryLaw M) := by
  constructor
  exact Measure.haarMeasure_self

instance (M : ℕ) : (sourceUnitaryLaw M).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

/-- The first two columns of a Haar unitary form the source's two-frame. -/
def sourceTwoFrame {M : ℕ} (hM : 2 ≤ M) (U : SourceUnitary M) :
    Matrix (Fin M) (Fin 2) ℂ :=
  fun i j ↦ U.val i (Fin.castLE hM j)

theorem sourceTwoFrame_orthonormal {M : ℕ} (hM : 2 ≤ M) (U : SourceUnitary M) :
    (sourceTwoFrame hM U)ᴴ * sourceTwoFrame hM U = 1 := by
  ext i j
  have h := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self U)
    (Fin.castLE hM i)) (Fin.castLE hM j)
  simpa [sourceTwoFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.star_eq_conjTranspose, Matrix.one_apply, Fin.castLE_inj] using h

theorem continuous_sourceTwoFrame {M : ℕ} (hM : 2 ≤ M) :
    Continuous (sourceTwoFrame hM) := by
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply (Fin.castLE hM j)).comp
      ((continuous_apply i).comp continuous_subtype_val)

/-- Coordinates (U^* a_i), with (a_i^*) stored as the row of (A). -/
def sourceProjectedRow {M : ℕ} (hM : 2 ≤ M)
    (U : SourceUnitary M) (a : Fin M → ℂ) : Fin 2 → ℂ :=
  fun j ↦ ∑ i, star (sourceTwoFrame hM U i j) * star (a i)

theorem continuous_sourceProjectedRow {M : ℕ} (hM : 2 ≤ M) :
    Continuous (fun p : SourceUnitary M × (Fin M → ℂ) ↦
      sourceProjectedRow hM p.1 p.2) := by
  apply continuous_pi
  intro j
  exact continuous_finsetSum _ fun i _ ↦
    (((continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_sourceTwoFrame hM).comp continuous_fst))).star).mul
        (((continuous_apply i).comp continuous_snd).star)

/-- Haar mixture of row likelihoods, as in (3.5). -/
def sourceLikelihood {M : ℕ} (hM : 2 ≤ M)
    (f : (Fin 2 → ℂ) → ℝ) (A : Frame (sourceRowCount M) M) : ℝ :=
  ∫ U, ∏ i, f (sourceProjectedRow hM U (A i)) ∂sourceUnitaryLaw M

def sourcePlantedLikelihood {M : ℕ} (hM : 2 ≤ M) :
    (Frame (sourceRowCount M) M) → ℝ :=
  sourceLikelihood hM (sourcePlantedDensity M)

def sourceReferenceLikelihood {M : ℕ} (hM : 2 ≤ M) :
    (Frame (sourceRowCount M) M) → ℝ :=
  sourceLikelihood hM (sourceReferenceDensity M)

theorem measurable_sourceLikelihood {M : ℕ} (hM : 2 ≤ M)
    {f : (Fin 2 → ℂ) → ℝ} (hf : Measurable f) :
    Measurable (sourceLikelihood hM f) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_prod
  intro i _
  apply hf.comp
  exact (continuous_sourceProjectedRow hM).measurable.comp
    (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))

theorem sourceLikelihood_nonneg {M : ℕ} (hM : 2 ≤ M)
    {f : (Fin 2 → ℂ) → ℝ} (hf : ∀ z, 0 ≤ f z)
    (A : Frame (sourceRowCount M) M) :
    0 ≤ sourceLikelihood hM f A :=
  integral_nonneg (fun _ ↦ Finset.prod_nonneg (fun _ _ ↦ hf _))

theorem sourceLikelihood_le {M : ℕ} (hM : 2 ≤ M)
    {f : (Fin 2 → ℂ) → ℝ} (hf : Measurable f)
    {B : ℝ} (hbound : ∀ z, 0 ≤ f z ∧ f z ≤ B)
    (A : Frame (sourceRowCount M) M) :
    sourceLikelihood hM f A ≤ B ^ sourceRowCount M := by
  have hmeas : Measurable (fun U : SourceUnitary M ↦
      ∏ i, f (sourceProjectedRow hM U (A i))) := by
    apply Finset.measurable_prod
    intro i _
    exact hf.comp ((continuous_sourceProjectedRow hM).measurable.comp
      (measurable_id.prodMk measurable_const))
  have hdom : ∀ U : SourceUnitary M,
      ‖∏ i, f (sourceProjectedRow hM U (A i))‖ ≤ B ^ sourceRowCount M := by
    intro U
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Finset.prod_nonneg (fun _ _ ↦ (hbound _).1))]
    simpa using Finset.prod_le_prod
      (fun i (_ : i ∈ Finset.univ) ↦ (hbound (sourceProjectedRow hM U (A i))).1)
      (fun i (_ : i ∈ Finset.univ) ↦ (hbound (sourceProjectedRow hM U (A i))).2)
  unfold sourceLikelihood
  calc
    _ ≤ ∫ _, B ^ sourceRowCount M ∂sourceUnitaryLaw M := by
      apply integral_mono
        (Integrable.of_bound hmeas.aestronglyMeasurable (B ^ sourceRowCount M)
          (Filter.Eventually.of_forall hdom))
        (integrable_const _)
      intro U
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hdom U)
    _ = _ := by simp

end HaarLikelihood

section LikelihoodSecondMoment

open MeasureTheory
open scoped BigOperators

/-- Fubini and iid rows give the replica identity before changing to overlap coordinates. -/
theorem iid_mixture_second_moment
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (ν : Measure Θ) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f g : Θ → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {B C : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hfb : ∀ θ x, 0 ≤ f θ x ∧ f θ x ≤ B)
    (hgb : ∀ θ x, 0 ≤ g θ x ∧ g θ x ≤ C) (N : ℕ) :
    (∫ A : Fin N → X,
      (∫ θ, ∏ i, f θ (A i) ∂ν) * (∫ θ, ∏ i, g θ (A i) ∂ν)
        ∂Measure.pi (fun _ ↦ μ)) =
      ∫ p : Θ × Θ, (∫ x, f p.1 x * g p.2 x ∂μ) ^ N ∂ν.prod ν := by
  let F : (Fin N → X) × (Θ × Θ) → ℝ :=
    fun p ↦ ∏ i, f p.2.1 (p.1 i) * g p.2.2 (p.1 i)
  have hmeas : Measurable F := by
    apply Finset.measurable_prod
    intro i _
    exact (hf.comp (((measurable_fst.comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp measurable_fst)))).mul
        (hg.comp (((measurable_snd.comp measurable_snd).prodMk
          ((measurable_pi_apply i).comp measurable_fst))))
  have hF : Integrable F ((Measure.pi (fun _ : Fin N ↦ μ)).prod (ν.prod ν)) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable ((B * C) ^ N)
    filter_upwards with p
    change ‖∏ i, f p.2.1 (p.1 i) * g p.2.2 (p.1 i)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Finset.prod_nonneg (fun i _ ↦ mul_nonneg (hfb _ _).1 (hgb _ _).1))]
    calc
      _ ≤ ∏ _ : Fin N, B * C := by
        apply Finset.prod_le_prod
        · intro i _
          exact mul_nonneg (hfb _ _).1 (hgb _ _).1
        · intro i _
          exact mul_le_mul (hfb _ _).2 (hgb _ _).2 (hgb _ _).1 hB
      _ = _ := by simp
  calc
    _ = ∫ A : Fin N → X, ∫ p : Θ × Θ, F (A, p) ∂ν.prod ν
        ∂Measure.pi (fun _ ↦ μ) := by
      apply integral_congr_ae
      filter_upwards with A
      simpa only [F, Finset.prod_mul_distrib] using
        (integral_prod_mul (μ := ν) (ν := ν)
          (fun θ ↦ ∏ i : Fin N, f θ (A i)) (fun θ ↦ ∏ i : Fin N, g θ (A i))).symm
    _ = ∫ p : Θ × Θ, ∫ A : Fin N → X, F (A, p)
        ∂Measure.pi (fun _ ↦ μ) ∂ν.prod ν := integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      simpa only [F, Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ)
          (fun x ↦ f p.1 x * g p.2 x))

end LikelihoodSecondMoment

section SourceSecondMoments

open MeasureTheory
open scoped BigOperators

theorem sourcePlantedLikelihood_nonneg {M : ℕ} (hM : 2 ≤ M)
    (A : Frame (sourceRowCount M) M) :
    0 ≤ sourcePlantedLikelihood hM A :=
  sourceLikelihood_nonneg hM (sourcePlantedDensity_nonneg M) A

theorem sourceReferenceLikelihood_nonneg {M : ℕ} (hM : 2 ≤ M)
    (A : Frame (sourceRowCount M) M) :
    0 ≤ sourceReferenceLikelihood hM A :=
  sourceLikelihood_nonneg hM (fun z ↦ (sourceReferenceDensity_pos M z).le) A

theorem sourcePlantedLikelihood_le {M : ℕ} (hM : 2 ≤ M)
    (A : Frame (sourceRowCount M) M) :
    sourcePlantedLikelihood hM A ≤ (Real.exp 1 * (M : ℝ) ^ 52) ^ sourceRowCount M :=
  sourceLikelihood_le hM (measurable_sourcePlantedDensity M)
    (fun z ↦ ⟨sourcePlantedDensity_nonneg M z,
      sourcePlantedDensity_le (by lia) z⟩) A

theorem sourceReferenceLikelihood_le {M : ℕ} (hM : 2 ≤ M)
    (A : Frame (sourceRowCount M) M) :
    sourceReferenceLikelihood hM A ≤ 4 ^ sourceRowCount M :=
  sourceLikelihood_le hM (measurable_sourceReferenceDensity M)
    (fun z ↦ ⟨(sourceReferenceDensity_pos M z).le, sourceReferenceDensity_le_four hM z⟩) A

theorem measurable_sourcePlantedLikelihood {M : ℕ} (hM : 2 ≤ M) :
    Measurable (sourcePlantedLikelihood hM) :=
  measurable_sourceLikelihood hM (measurable_sourcePlantedDensity M)

theorem measurable_sourceReferenceLikelihood {M : ℕ} (hM : 2 ≤ M) :
    Measurable (sourceReferenceLikelihood hM) :=
  measurable_sourceLikelihood hM (measurable_sourceReferenceDensity M)

private theorem integrable_mul_of_bounded_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, 0 ≤ f x ∧ f x ≤ B) (hC : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    Integrable (fun x ↦ f x * g x) μ := by
  apply Integrable.of_bound (hf.mul hg).aestronglyMeasurable (B * C)
  filter_upwards with x
  change ‖f x * g x‖ ≤ B * C
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hB x).1 (hC x).1)]
  exact mul_le_mul (hB x).2 (hC x).2 (hC x).1 ((hB x).1.trans (hB x).2)

/-- All three second moments exist for the actual likelihoods (3.5). -/
theorem integrable_sourceLikelihood_products {M : ℕ} (hM : 2 ≤ M) :
    Integrable (fun A ↦ sourcePlantedLikelihood hM A * sourcePlantedLikelihood hM A)
      (standardComplexGaussianFrame (sourceRowCount M) M) ∧
    Integrable (fun A ↦ sourceReferenceLikelihood hM A * sourceReferenceLikelihood hM A)
      (standardComplexGaussianFrame (sourceRowCount M) M) ∧
    Integrable (fun A ↦ sourcePlantedLikelihood hM A * sourceReferenceLikelihood hM A)
      (standardComplexGaussianFrame (sourceRowCount M) M) := by
  have hg := measurable_sourcePlantedLikelihood hM
  have hr := measurable_sourceReferenceLikelihood hM
  have hgb : ∀ A, 0 ≤ sourcePlantedLikelihood hM A ∧
      sourcePlantedLikelihood hM A ≤ (Real.exp 1 * (M : ℝ) ^ 52) ^ sourceRowCount M := fun A ↦ ⟨sourcePlantedLikelihood_nonneg hM A, sourcePlantedLikelihood_le hM A⟩
  have hrb : ∀ A, 0 ≤ sourceReferenceLikelihood hM A ∧
      sourceReferenceLikelihood hM A ≤ 4 ^ sourceRowCount M := fun A ↦ ⟨sourceReferenceLikelihood_nonneg hM A, sourceReferenceLikelihood_le hM A⟩
  exact ⟨integrable_mul_of_bounded_nonneg hg hg hgb hgb,
    integrable_mul_of_bounded_nonneg hr hr hrb hrb,
    integrable_mul_of_bounded_nonneg hg hr hgb hrb⟩

/-- The quantity bounded in Proposition 3.2, with the source likelihoods and Gaussian law. -/
def sourceLikelihoodL2 (M : ℕ) (hM : 2 ≤ M) : ℝ :=
  ∫ A, (sourcePlantedLikelihood hM A - sourceReferenceLikelihood hM A) ^ 2
    ∂standardComplexGaussianFrame (sourceRowCount M) M

theorem sourceLikelihoodL2_nonneg (M : ℕ) (hM : 2 ≤ M) :
    0 ≤ sourceLikelihoodL2 M hM :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

theorem sourceLikelihoodL2_identity (M : ℕ) (hM : 2 ≤ M) :
    sourceLikelihoodL2 M hM =
      (∫ A, sourcePlantedLikelihood hM A * sourcePlantedLikelihood hM A
        ∂standardComplexGaussianFrame (sourceRowCount M) M) +
      (∫ A, sourceReferenceLikelihood hM A * sourceReferenceLikelihood hM A
        ∂standardComplexGaussianFrame (sourceRowCount M) M) -
      2 * (∫ A, sourcePlantedLikelihood hM A * sourceReferenceLikelihood hM A
        ∂standardComplexGaussianFrame (sourceRowCount M) M) := by
  obtain ⟨hgg, hrr, hgr⟩ := integrable_sourceLikelihood_products hM
  unfold sourceLikelihoodL2
  calc
    _ = ∫ A, (sourcePlantedLikelihood hM A * sourcePlantedLikelihood hM A +
        sourceReferenceLikelihood hM A * sourceReferenceLikelihood hM A) -
        2 * (sourcePlantedLikelihood hM A * sourceReferenceLikelihood hM A)
        ∂standardComplexGaussianFrame (sourceRowCount M) M := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = _ := by
      have hsub := integral_sub (hgg.add hrr) (hgr.const_mul (2 : ℝ))
      simp only [Pi.add_apply] at hsub
      rw [hsub, integral_add hgg hrr, integral_const_mul]

end SourceSecondMoments

end NLA.FR05
