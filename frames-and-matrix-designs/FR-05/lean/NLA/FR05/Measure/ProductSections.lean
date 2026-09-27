/-
A product-measure assembly lemma for the conditional small-ball argument.

The source row law is a product of scalar planted coordinates and an
independent complex-Gaussian tail.  This records the Tonelli step which turns
a uniform conditional tail estimate into an estimate under the full product
law.
-/
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- A uniform upper bound on all right-hand sections of a measurable set
gives the same bound under a product law whose left marginal is a probability
measure. -/
theorem prod_measure_le_of_sections_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν]
    {s : Set (α × β)} (hs : MeasurableSet s) (c : ℝ≥0∞)
    (hsection : ∀ x : α, ν {y | (x, y) ∈ s} ≤ c) :
    (μ.prod ν) s ≤ c := by
  rw [Measure.prod_apply hs]
  grw [show ∀ x, ν (Prod.mk x ⁻¹' s) ≤ c from hsection]
  simp

end NLA.FR05
