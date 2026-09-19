/-
Original mathematics and exact seed: Sidney Holden, Flatiron Institute,
Simons Foundation. Formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology; Codex assistance.

C01 of the frozen PF03 statement package. Only three fixed rational endpoint
inequalities are computed. The real root follows from the library rpow identity
and monotonicity; no interval search or approximation to rpow is needed.
-/
import NLA.PF03.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.PF03

lemma root_lower_positive : (0 : ℝ) < (ell : ℝ) := by
  unfold ell
  interval_decide (trust := kernel)

set_option trace.interval_decide true in
lemma root_lower_cube : (ell : ℝ) ^ 3 < 2 := by
  unfold ell
  -- One 160-bit checked enclosure resolves the 40-digit endpoint margin.
  -- Keep the rational cast intact, avoiding a separately rounded reciprocal
  -- of 10^40 followed by multiplication by a 40-digit numerator.
  -- This entry point must accept a kernel certificate; no fallback is allowed.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    match ← LeanCert.Tactic.Auto.proveClosedExpressionBoundTyped
        goal (← goal.getType) 0 (-160) false with
    | .ok _ => pure ()
    | .error _ => Lean.throwError "PF03 lower endpoint certificate was not accepted"

set_option trace.interval_decide true in
lemma root_upper_cube : (2 : ℝ) < (upp : ℝ) ^ 3 := by
  unfold upp
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    match ← LeanCert.Tactic.Auto.proveClosedExpressionBoundTyped
        goal (← goal.getType) 0 (-160) false with
    | .ok _ => pure ()
    | .error _ => Lean.throwError "PF03 upper endpoint certificate was not accepted"

/-- The positive real cube root and the exact strict rational enclosure. -/
theorem alpha_certificate :
    alpha ^ 3 = 2 ∧ 0 < alpha ∧ (ell : ℝ) < alpha ∧ alpha < (upp : ℝ) := by
  have ha : 0 < alpha := Real.rpow_pos_of_pos (by norm_num) _
  have hc : alpha ^ 3 = 2 := by
    unfold alpha
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 3)
        (by norm_num) (by decide))
  have hl : (ell : ℝ) < alpha := by
    by_contra hn
    have hp := pow_le_pow_left₀ ha.le (le_of_not_gt hn) 3
    rw [hc] at hp
    exact (not_le_of_gt root_lower_cube) hp
  have hu : alpha < (upp : ℝ) := by
    by_contra hn
    have hupper0 : (0 : ℝ) ≤ (upp : ℝ) := by
      have : (ell : ℝ) ≤ (upp : ℝ) := by
        unfold ell upp
        push_cast
        norm_num
      exact le_trans root_lower_positive.le this
    have hp := pow_le_pow_left₀ hupper0 (le_of_not_gt hn) 3
    rw [hc] at hp
    exact (not_le_of_gt root_upper_cube) hp
  exact ⟨hc, ha, hl, hu⟩

#print axioms alpha_certificate
#assert_trust kernel alpha_certificate

end NLA.PF03
