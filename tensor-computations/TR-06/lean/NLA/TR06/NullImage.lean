/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Rectangular
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal
open MeasureTheory Set
namespace NLA.TR06

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

-- Keep the independently reviewed finite-dimensional target interface.
-- The proof only uses its metric and Borel structures.
set_option linter.unusedSectionVars false in
/-- A C1 map sends an arbitrary Lebesgue-null source set to a set null for
normalized Hausdorff measure in the SOURCE dimension. No injectivity,
source measurability, or tensor-specific regularity premise is assumed. -/
theorem contDiff_image_null (f : E → F) (s : Set E)
    (hf : ContDiff ℝ 1 f) (hs : (volume : Measure E) s = 0) :
    (μHE[Module.finrank ℝ E] : Measure F) (f '' s) = 0 := by
  have hball (j : ℕ) :
      (μHE[Module.finrank ℝ E] : Measure F)
        (f '' (s ∩ Metric.closedBall 0 (j : ℝ))) = 0 := by
    obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall (0 : E) (j : ℝ)) (isCompact_closedBall (0 : E) (j : ℝ))
    have hsource : (μHE[Module.finrank ℝ E] : Measure E)
        (s ∩ Metric.closedBall 0 (j : ℝ)) = 0 := by
      rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact measure_mono_null inter_subset_left hs
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ (K : ℝ≥0∞) ^ Module.finrank ℝ E *
          (μHE[Module.finrank ℝ E] : Measure E)
            (s ∩ Metric.closedBall 0 (j : ℝ)) :=
        Area.euclidean_image_le_of_lipschitzOn (hK.mono inter_subset_right) _
      _ = 0 := by rw [hsource, mul_zero]
  have hexhaust : f '' s = ⋃ j : ℕ, f '' (s ∩ Metric.closedBall 0 (j : ℝ)) := by
    rw [← Set.image_iUnion, Metric.iUnion_inter_closedBall_nat s (0 : E)]
  rw [hexhaust]
  exact measure_iUnion_null hball

#print axioms contDiff_image_null
#assert_trust kernel contDiff_image_null
end NLA.TR06
