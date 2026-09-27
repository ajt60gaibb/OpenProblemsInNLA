/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The reference Gaussian mixture has likelihood (3.5), and its injectivity
probability is the original Gaussian probability.
-/
import NLA.FR05.Bridges.SourceReferenceFrameDensity

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace NLA.FR05

def sourceOrientedReferenceDensity (M : ℕ) {m n : ℕ}
    (U : SourceUnitary (n + 2)) (A : Frame m (n + 2)) : ℝ :=
  ∏ i, sourceReferenceDensity M (sourceProjectedRow (by lia) U (A i))

@[fun_prop] theorem measurable_sourceOrientedReferenceDensity (M m n : ℕ) :
    Measurable (fun p : SourceUnitary (n + 2) × Frame m (n + 2) ↦
      sourceOrientedReferenceDensity M p.1 p.2) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_sourceReferenceDensity M).comp
    ((continuous_sourceProjectedRow (by lia)).measurable.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

theorem sourceOrientedReferenceDensity_nonneg (M : ℕ) {m n : ℕ}
    (U : SourceUnitary (n + 2)) (A : Frame m (n + 2)) :
    0 ≤ sourceOrientedReferenceDensity M U A :=
  Finset.prod_nonneg fun _ _ ↦ (sourceReferenceDensity_pos M _).le

theorem integrable_sourceOrientedReferenceDensity {M m n : ℕ} (hM : 2 ≤ M)
    (A : Frame m (n + 2)) :
    Integrable (fun U ↦ sourceOrientedReferenceDensity M U A) (sourceUnitaryLaw (n + 2)) := by
  have hmeas : Measurable (fun U : SourceUnitary (n + 2) ↦
      sourceOrientedReferenceDensity M U A) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_sourceReferenceDensity M).comp
      ((continuous_sourceProjectedRow (by lia)).measurable.comp
        (measurable_id.prodMk measurable_const))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (4 ^ m)
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceOrientedReferenceDensity_nonneg M U A)]
  calc
    _ ≤ ∏ _ : Fin m, (4 : ℝ) :=
      Finset.prod_le_prod (fun _ _ ↦ (sourceReferenceDensity_pos M _).le)
        (fun _ _ ↦ sourceReferenceDensity_le_four hM _)
    _ = _ := by simp

theorem sourceReferenceFrameLaw_map_unitary_eq_withDensity {M m n : ℕ}
    (hM : 2 ≤ M) (U : SourceUnitary (n + 2)) :
    (sourceReferenceFrameLaw M m n).map (fun A ↦ A * (star U).val) =
      (standardComplexGaussianFrame m (n + 2)).withDensity
        (fun A ↦ ENNReal.ofReal (sourceOrientedReferenceDensity M U A)) := by
  rw [sourceReferenceFrameLaw_eq_withDensity hM]
  have he : (fun A : Frame m (n + 2) ↦ ENNReal.ofReal
      (∏ i, sourceReferenceDensity M (sourceHead (star (A i))))) =
      fun A ↦ ENNReal.ofReal (sourceOrientedReferenceDensity M U (A * (star U).val)) := by
    funext A
    simp only [sourceOrientedReferenceDensity, ← sourceHead_star_frame_mul,
      Matrix.mul_assoc, show (star U).val * U.val = 1 from Matrix.UnitaryGroup.star_mul_self U,
      Matrix.mul_one]
  rw [he, map_withDensity_comp _ (fun A : Frame m (n + 2) ↦ A * (star U).val)
      (show Measurable (fun A : Frame m (n + 2) ↦ A * (star U).val) from
        measurable_frame_mul_unitary.comp (measurable_const.prodMk measurable_id))
      (fun A ↦ ENNReal.ofReal (sourceOrientedReferenceDensity M U A))
      (((measurable_sourceOrientedReferenceDensity M m n).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal),
    standardComplexGaussianFrame_map_mul_unitary]

/-- Scale a standard Gaussian frame in two coordinates and independently
sample its Haar orientation. -/
def sourceHaarReferenceFrameLaw (M m n : ℕ) : Measure (Frame m (n + 2)) :=
  ((sourceUnitaryLaw (n + 2)).prod (sourceReferenceFrameLaw M m n)).map
    (fun p ↦ p.2 * p.1.val)

theorem sourceHaarReferenceFrameLaw_eq_withDensity {M m n : ℕ} (hM : 2 ≤ M) :
    sourceHaarReferenceFrameLaw M m n =
      (standardComplexGaussianFrame m (n + 2)).withDensity
        (fun A ↦ ENNReal.ofReal (∫ U, sourceOrientedReferenceDensity M U A
          ∂sourceUnitaryLaw (n + 2))) := by
  exact Measure.map_prod_eq_withDensity_of_inv (sourceUnitaryLaw (n + 2))
    (standardComplexGaussianFrame m (n + 2)) (sourceReferenceFrameLaw M m n)
    (fun U A ↦ A * U.val) measurable_frame_mul_unitary
    (sourceOrientedReferenceDensity M) (measurable_sourceOrientedReferenceDensity M m n)
    (sourceOrientedReferenceDensity_nonneg M) (integrable_sourceOrientedReferenceDensity hM)
    (sourceReferenceFrameLaw_map_unitary_eq_withDensity hM)

theorem sourceHaarReferenceFrameLaw_injective_eq (M m n : ℕ) :
    sourceHaarReferenceFrameLaw M m n {A | PhaseRetrievalInjective A} =
      standardComplexGaussianFrame m (n + 2) {A | PhaseRetrievalInjective A} := by
  have hs : MeasurableSet {A : Frame m (n + 2) | PhaseRetrievalInjective A} :=
    measurableSet_phaseRetrievalInjective m (n + 2)
  have he : (fun p : SourceUnitary (n + 2) × Frame m (n + 2) ↦ p.2 * p.1.val) ⁻¹'
      {A | PhaseRetrievalInjective A} = Set.univ ×ˢ {A | PhaseRetrievalInjective A} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
    exact phaseRetrievalInjective_mul_unitary p.2 p.1
  rw [sourceHaarReferenceFrameLaw, Measure.map_apply
      (show Measurable (fun p : SourceUnitary (n + 2) × Frame m (n + 2) ↦
        p.2 * p.1.val) from measurable_frame_mul_unitary) hs,
    he, Measure.prod_prod, measure_univ, one_mul, sourceReferenceFrameLaw,
    Measure.map_apply (measurable_sourceReferenceFrame M m n) hs]
  congr 1
  ext A
  exact phaseRetrievalInjective_referenceFrame M A

/-- The reference sampler at the original ambient dimension and row count. -/
def sourceHaarReferenceFrameLawAt (M : ℕ) (hM : 2 ≤ M) :
    Measure (Frame (sourceRowCount M) M) :=
  (sourceHaarReferenceFrameLaw M (sourceRowCount M) (sourceTailDimension M)).map
    (sourceFrameAtDimension hM)

theorem sourceHaarReferenceFrameLawAt_eq_likelihood {M : ℕ} (hM : 2 ≤ M) :
    sourceHaarReferenceFrameLawAt M hM =
      (standardComplexGaussianFrame (sourceRowCount M) M).withDensity
        (fun A ↦ ENNReal.ofReal (sourceReferenceLikelihood hM A)) := by
  have transport (M n : ℕ) (hM : 2 ≤ M) (hd : n + 2 = M) :
      (sourceHaarReferenceFrameLaw M (sourceRowCount M) n).map
          (fun A : Frame (sourceRowCount M) (n + 2) ↦
            fun i j ↦ A i (Fin.cast hd.symm j)) =
        (standardComplexGaussianFrame (sourceRowCount M) M).withDensity
          (fun A ↦ ENNReal.ofReal (sourceReferenceLikelihood hM A)) := by
    subst M
    change Measure.map id _ = _
    rw [Measure.map_id]
    exact sourceHaarReferenceFrameLaw_eq_withDensity hM
  exact transport M (sourceTailDimension M) hM (sourceTailDimension_add_two hM)

theorem sourceHaarReferenceFrameLawAt_injective_eq {M : ℕ} (hM : 2 ≤ M) :
    sourceHaarReferenceFrameLawAt M hM {A | PhaseRetrievalInjective A} =
      standardComplexGaussianFrame (sourceRowCount M) M {A | PhaseRetrievalInjective A} := by
  have transport (M n : ℕ) (hd : n + 2 = M) :
      ((sourceHaarReferenceFrameLaw M (sourceRowCount M) n).map
        (fun A : Frame (sourceRowCount M) (n + 2) ↦
          fun i j ↦ A i (Fin.cast hd.symm j))) {A | PhaseRetrievalInjective A} =
        standardComplexGaussianFrame (sourceRowCount M) M {A | PhaseRetrievalInjective A} := by
    subst M
    change (Measure.map id _) _ = _
    rw [Measure.map_id]
    exact sourceHaarReferenceFrameLaw_injective_eq _ _ _
  exact transport M (sourceTailDimension M) (sourceTailDimension_add_two hM)

/-- Reweighting by the reference likelihood leaves the original injectivity
probability unchanged. This is the reference-event identity used in the
source's final Cauchy--Schwarz argument. -/
theorem sourceReferenceLikelihood_injective_probability {M : ℕ} (hM : 2 ≤ M) :
    ((standardComplexGaussianFrame (sourceRowCount M) M).withDensity
      (fun A ↦ ENNReal.ofReal (sourceReferenceLikelihood hM A))).real
        {A | PhaseRetrievalInjective A} = phaseRetrievalProbability M := by
  rw [← sourceHaarReferenceFrameLawAt_eq_likelihood hM, Measure.real_def,
    sourceHaarReferenceFrameLawAt_injective_eq hM]
  rfl

/-- Integral form of the reference-event identity. -/
theorem integral_sourceReferenceLikelihood_injective {M : ℕ} (hM : 2 ≤ M) :
    (∫ A in {A | PhaseRetrievalInjective A}, sourceReferenceLikelihood hM A
      ∂standardComplexGaussianFrame (sourceRowCount M) M) = phaseRetrievalProbability M := by
  rw [← sourceReferenceLikelihood_injective_probability hM, Measure.real_def,
    withDensity_apply _ (show MeasurableSet
      {A : Frame (sourceRowCount M) M | PhaseRetrievalInjective A} from
        measurableSet_phaseRetrievalInjective _ _)]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (sourceLikelihood_nonneg hM
      (fun z ↦ (sourceReferenceDensity_pos M z).le)))
    (measurable_sourceLikelihood hM (measurable_sourceReferenceDensity M)).aestronglyMeasurable

end NLA.FR05
