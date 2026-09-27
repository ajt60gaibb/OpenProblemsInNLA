/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLA.FR05.Proposition31

/-!
# Haar rotations preserve the planted failure estimate

The joint frame action is measurable and preserves injectivity by the general
change-of-coordinates theorem. These facts transport Proposition 3.1 from the
canonical planted sampler to its independently Haar-rotated version.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.Elementwise
namespace NLA.FR05

/-- Joint measurability of right multiplication of a frame by a unitary matrix. -/
@[fun_prop]
theorem measurable_frame_mul_unitary {m d : ℕ} :
    Measurable (fun p : SourceUnitary d × Frame m d ↦ p.2 * p.1.val) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  have hu : Measurable (fun U : SourceUnitary d ↦ U.val k j) := by
    have hc : Continuous (fun U : SourceUnitary d ↦ U.val k j) := by
      exact (continuous_apply j).comp ((continuous_apply k).comp continuous_subtype_val)
    exact hc.measurable
  have ha : Measurable (fun p : SourceUnitary d × Frame m d ↦ p.2 i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)
  exact ha.mul (hu.comp measurable_fst)

/-- A unitary change of signal coordinates preserves phase-retrieval injectivity. -/
theorem phaseRetrievalInjective_mul_unitary {m d : ℕ}
    (A : Frame m d) (U : SourceUnitary d) :
    PhaseRetrievalInjective (A * U.val) ↔ PhaseRetrievalInjective A := by
  exact phaseRetrievalInjective_iff_of_linearEquiv A (A * U.val)
    (Matrix.UnitaryGroup.toLinearEquiv U) (sameMeasurements_mul A U.val)

/-- Sample the canonical planted frame and then its independent Haar orientation. -/
def sourceHaarPlantedFrameLawAt (M : ℕ) :
    Measure (Frame (sourceRowCount M) (sourceTailDimension M + 2)) :=
  ((sourceUnitaryLaw (sourceTailDimension M + 2)).prod (sourcePlantedFrameLawAt M)).map
    (fun p ↦ p.2 * p.1.val)

theorem sourceHaarPlantedFrameLaw_injective_eq {M : ℕ} (hM : 1 ≤ M) :
    sourceHaarPlantedFrameLawAt M {A | PhaseRetrievalInjective A} =
      sourcePlantedFrameLawAt M {A | PhaseRetrievalInjective A} := by
  let _ := isProbabilityMeasure_sourcePlantedFrameLawAt hM
  have hm : Measurable (fun p : SourceUnitary (sourceTailDimension M + 2) ×
      Frame (sourceRowCount M) (sourceTailDimension M + 2) ↦ p.2 * p.1.val) :=
    measurable_frame_mul_unitary
  have he : (fun p : SourceUnitary (sourceTailDimension M + 2) ×
      Frame (sourceRowCount M) (sourceTailDimension M + 2) ↦ p.2 * p.1.val) ⁻¹'
      {A | PhaseRetrievalInjective A} =
      Set.univ ×ˢ {A | PhaseRetrievalInjective A} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
    exact phaseRetrievalInjective_mul_unitary p.2 p.1
  unfold sourceHaarPlantedFrameLawAt
  rw [Measure.map_apply hm (show MeasurableSet
    {A : Frame (sourceRowCount M) (sourceTailDimension M + 2) | PhaseRetrievalInjective A}
      from measurableSet_phaseRetrievalInjective _ _), he, Measure.prod_prod]
  simp

theorem proposition_3_1_haar :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, 2 ≤ D ∧ ∀ M : ℕ, D ≤ M →
      (sourceHaarPlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} ≤
        C / (M : ℝ) ^ 2 := by
  obtain ⟨C, hC, D, hD, h⟩ := proposition_3_1
  refine ⟨C, hC, D, hD, fun M hM ↦ ?_⟩
  rw [Measure.real_def, sourceHaarPlantedFrameLaw_injective_eq (by lia)]
  exact h M hM
end NLA.FR05
