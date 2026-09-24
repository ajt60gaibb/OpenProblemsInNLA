/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.LocusMeasurability
import NLA.TR06.MetricSlope
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.AEMeasurable

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal
open Set MeasureTheory Filter Topology
namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Every fixed-direction ratio is continuous on an actual C1 chart source.
The zero tangent direction is handled by the original real zero-division
convention; all nonzero directions have a nonzero input differential. -/
theorem continuousOn_chart_directionalRatio (c : DecompositionChart d n r)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) :
    ContinuousOn (fun u => ENNReal.ofReal
      (‖fderiv ℝ (fun w => normalizedTuple (c.summands w)) u v‖ /
        ‖fderiv ℝ (fun w => (c.chart w).val) u v‖)) c.chart.source := by
  by_cases hv : v = 0
  · simp only [hv, map_zero, norm_zero, div_zero, ENNReal.ofReal_zero]
    exact continuousOn_const
  · have hinput := c.input_smooth.continuousOn_fderiv_of_isOpen c.chart.open_source le_rfl
    have houtput := c.output_smooth.continuousOn_fderiv_of_isOpen c.chart.open_source le_rfl
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply (houtput.clm_apply continuousOn_const).norm.div
      (hinput.clm_apply continuousOn_const).norm
    intro u hu
    apply norm_ne_zero_iff.mpr
    intro heq
    apply hv
    apply c.input_injective_derivative u hu
    simpa only [map_zero] using heq

/-- The full derivative-ratio supremum is lower semicontinuous, without
replacing its tangent-vector indexing by an assumed finite or countable set. -/
theorem lowerSemicontinuousOn_chart_derivativeRatio (c : DecompositionChart d n r) :
    LowerSemicontinuousOn (fun u => derivativeRatio
      (fderiv ℝ (fun w => (c.chart w).val) u)
      (fderiv ℝ (fun w => normalizedTuple (c.summands w)) u)) c.chart.source := by
  unfold derivativeRatio
  exact lowerSemicontinuousOn_iSup fun v =>
    (continuousOn_chart_directionalRatio c v).lowerSemicontinuousOn

private theorem lowerSemicontinuousOn_angularSlope_chart_target
    (c : DecompositionChart d n r) :
    LowerSemicontinuousOn (fun A : identifiableRealSet d n r => angularSlope r A.val)
      c.chart.target := by
  have hcomp := (lowerSemicontinuousOn_chart_derivativeRatio c).comp
    c.chart.continuousOn_symm (fun B hB => c.chart.map_target hB)
  intro A hA
  apply LowerSemicontinuousWithinAt.congr_of_eventuallyEq (hcomp A hA) hA
  filter_upwards [self_mem_nhdsWithin] with B hB
  change derivativeRatio
    (fderiv ℝ (fun w => (c.chart w).val) (c.chart.symm B))
    (fderiv ℝ (fun w => normalizedTuple (c.summands w)) (c.chart.symm B)) =
      angularSlope r B.val
  rw [← angularSlope_eq_chart_derivative c (c.chart.symm B) (c.chart.map_target hB),
    c.chart.right_inv hB]

/-- The intrinsic angular slope is lower semicontinuous on the actual C1
regular locus, using an open chart target around each locus point. -/
theorem lowerSemicontinuous_angularSlope_regularSet :
    LowerSemicontinuous (fun A : regularSet d n r => angularSlope r A.val) := by
  let inclusion : regularSet d n r → identifiableRealSet d n r :=
    Set.inclusion regularSet_subset_identifiable
  have hinc : Continuous inclusion := continuous_inclusion _
  intro A
  rcases A.property with ⟨c, u, hu, heq⟩
  have hchart : c.chart u = inclusion A := Subtype.ext heq
  have htarget : inclusion A ∈ c.chart.target := hchart ▸ c.chart.map_source hu
  have hwithin := lowerSemicontinuousOn_angularSlope_chart_target c (inclusion A) htarget
  have hat : LowerSemicontinuousAt
      (fun B : identifiableRealSet d n r => angularSlope r B.val) (inclusion A) := by
    intro b hb
    simpa only [nhdsWithin_eq_nhds.mpr (c.chart.open_target.mem_nhds htarget)] using hwithin b hb
  exact hat.comp hinc.continuousAt

/-- Borel measurability on the regular locus, with its actual subspace Borel
structure and the frozen extended angular-slope definition. -/
theorem measurable_angularSlope_regularSet :
    Measurable (fun A : regularSet d n r => angularSlope r A.val) :=
  lowerSemicontinuous_angularSlope_regularSet.measurable

/-- Angular-slope measurability for the induced-volume candidate restricted
to the actual C1 chart locus. No genericity or full-measure premise is used. -/
theorem aemeasurable_angularSlope_regularVolume (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    AEMeasurable (angularSlope (d := d) (n := n) r) (regularVolume d n r) := by
  exact aemeasurable_restrict_of_measurable_subtype (measurableSet_regularSet d n r)
    measurable_angularSlope_regularSet

#print axioms continuousOn_chart_directionalRatio
#print axioms lowerSemicontinuousOn_chart_derivativeRatio
#print axioms lowerSemicontinuous_angularSlope_regularSet
#print axioms measurable_angularSlope_regularSet
#print axioms aemeasurable_angularSlope_regularVolume
#assert_trust kernel continuousOn_chart_directionalRatio
#assert_trust kernel lowerSemicontinuousOn_chart_derivativeRatio
#assert_trust kernel lowerSemicontinuous_angularSlope_regularSet
#assert_trust kernel measurable_angularSlope_regularSet
#assert_trust kernel aemeasurable_angularSlope_regularVolume
end NLA.TR06
