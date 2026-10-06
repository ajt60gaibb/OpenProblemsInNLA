import NLA.IE06.Statements
import Mathlib.Tactic

/-! Small semantic checks of the concrete model. None proves the IE-06 limit. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory
noncomputable section
namespace NLA.IE06

theorem gaussianMatrix_probability_proved (n : ℕ) :
    IsProbabilityMeasure (gaussianMatrix n) := by
  change IsProbabilityMeasure (Measure.pi
    (fun _ : Fin n => Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
  infer_instance

theorem exceedanceEvent_zero (t : ℝ) : exceedanceEvent 0 t = ∅ := by
  ext A
  simp [exceedanceEvent]

theorem exceedanceEvent_antitone (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    exceedanceEvent n t ⊆ exceedanceEvent n s := by
  rintro A ⟨hn, hdet, path, hp, hgrowth⟩
  exact ⟨hn, hdet, path, hp, hst.trans_lt hgrowth⟩

/-- A one-dimensional nonzero matrix has growth one, independently of the
path argument (there is only one map Fin 1 → Fin 1). -/
theorem growth_one (A : Mat 1) (path : PivotPath 1) (hA : A 0 0 ≠ 0) :
    growth A path = 1 := by
  simp [growth, activeMaxNN, trajectory, entryMax, entryMaxNN, hA]

#assert_trust kernel gaussianMatrix_probability_proved
#assert_trust kernel exceedanceEvent_zero
#assert_trust kernel exceedanceEvent_antitone
#assert_trust kernel growth_one
#print axioms gaussianMatrix_probability_proved
#print axioms exceedanceEvent_zero
#print axioms exceedanceEvent_antitone
#print axioms growth_one

end NLA.IE06
