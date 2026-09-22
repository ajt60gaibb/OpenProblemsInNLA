import NLA.IE22.DeterministicSchedule
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
open NLA.IE21 NLA.IE22

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (∀ᶠ n in atTop, 1 ≤ deletionSchedule n ∧ deletionSchedule n < n ∧
      0 < errorSchedule n ∧ errorSchedule n < 1 ∧
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) < 1) ∧
    Tendsto errorSchedule atTop (𝓝 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) ≤ C * errorSchedule n ∧
      deterministicBound θ n (deletionSchedule n) (errorSchedule n) - gaussianTrim θ ≤
        C * errorSchedule n := NLA.IE22.deterministic_schedule θ hθ

#print axioms NLA.IE22.errorSchedule_tendsto_zero

#print axioms NLA.IE22.schedule_power_identities

#print axioms NLA.IE22.schedule_dimension_bounds

#print axioms NLA.IE22.schedule_failure_bound

#print axioms NLA.IE22.schedule_deterministic_bound

#print axioms NLA.IE22.deterministic_schedule
