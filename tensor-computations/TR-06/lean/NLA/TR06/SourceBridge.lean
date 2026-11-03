/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.MetricSlope
import NLA.TR06.LinearNorm

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal
namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Forget only differentiability orders above one; every mathematical map,
chart, decomposition, metric and derivative remains identical. -/
def SmoothDecompositionChart.toC1 (c : SmoothDecompositionChart d n r) :
    DecompositionChart d n r where
  chart := c.chart
  summands := c.summands
  decomposes := c.decomposes
  input_smooth := c.input_smooth.of_le (by simp)
  summands_smooth := fun i => (c.summands_smooth i).of_le (by simp)
  output_smooth := c.output_smooth.of_le (by simp)
  input_injective_derivative := c.input_injective_derivative

/-- Every genuinely smooth decomposition chart is also a valid C1 chart. -/
theorem smoothRegularSet_subset_regularSet :
    smoothRegularSet d n r ⊆ regularSet d n r := by
  rintro A ⟨c, u, hu, heq⟩
  exact ⟨c.toC1, u, hu, heq⟩

/-- Each actual smooth inverse branch has the same angular derivative norm
as the intrinsic order-free metric slope. -/
theorem smooth_chart_operatorNorm_eq_angularSlope
    (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    ENNReal.ofReal ‖inducedDerivative
      (fderiv ℝ (fun v => (c.chart v).val) u)
      (fderiv ℝ (fun v => normalizedTuple (c.summands v)) u)
      (c.input_injective_derivative u hu)‖ = angularSlope r (c.chart u).val := by
  rw [← derivativeRatio_eq_operatorNorm]
  exact (angularSlope_eq_chart_derivative c.toC1 u hu).symm

/-- Taking the supremum over all smooth branches cannot increase the slope.
At points without branches the source convention contributes zero. -/
theorem sourceAngular_le_angularSlope (A : Tensor ℝ d n) :
    sourceAngular d n r A ≤ angularSlope r A := by
  unfold sourceAngular
  refine iSup_le fun c => iSup_le fun u => iSup_le fun hu => iSup_le fun heq => ?_
  rw [smooth_chart_operatorNorm_eq_angularSlope c u hu, heq]

/-- Exact source/metric correspondence on the actual smooth inverse locus.
The separate full-measure theorem is still required before using this as an
a.e. source-volume statement. -/
theorem sourceAngular_eq_angularSlope_on_smoothRegularSet {A : Tensor ℝ d n}
    (hA : A ∈ smoothRegularSet d n r) : sourceAngular d n r A = angularSlope r A := by
  apply le_antisymm (sourceAngular_le_angularSlope A)
  rcases hA with ⟨c, u, hu, heq⟩
  rw [← heq, ← smooth_chart_operatorNorm_eq_angularSlope c u hu]
  exact le_iSup_of_le c (le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le rfl le_rfl)))

#print axioms smoothRegularSet_subset_regularSet
#print axioms sourceAngular_le_angularSlope
#print axioms sourceAngular_eq_angularSlope_on_smoothRegularSet
#assert_trust kernel smoothRegularSet_subset_regularSet
#assert_trust kernel sourceAngular_le_angularSlope
#assert_trust kernel sourceAngular_eq_angularSlope_on_smoothRegularSet
end NLA.TR06
