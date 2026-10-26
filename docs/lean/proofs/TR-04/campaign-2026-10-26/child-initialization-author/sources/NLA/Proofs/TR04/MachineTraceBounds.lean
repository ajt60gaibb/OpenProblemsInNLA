import NLA.Proofs.TR04.MachineTotality

/-! Exact charged prefixes and absorbing output states of the unchanged RAM.
These lemmas supply no assumed runtime or approximation guarantee. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem legalTrace_cost_eq {P : Program} {start : State P} {trace : Trace P}
    (h : LegalTrace P start trace) (t : ℕ) :
    trace.cost t = charge P (trace.state t) :=
  step_cost_eq (h.2 t)

theorem costThrough_zero (P : Program) (trace : Trace P) :
    CostThrough P trace 0 = 0 := by simp [CostThrough]

theorem costThrough_succ (P : Program) (trace : Trace P) (t : ℕ) :
    CostThrough P trace (t + 1) = CostThrough P trace t + trace.cost t := by
  simp [CostThrough, Finset.sum_range_succ]

theorem charge_pos_of_running {P : Program} {s : State P}
    (hs : s.status = .running) : 0 < charge P s := by
  cases hi : P.code s.label <;> simp [charge, hs, hi]

/-- A successful output is preserved along every later legal step. -/
theorem legalTrace_halted_state_add {P : Program} {start : State P}
    {trace : Trace P} (h : LegalTrace P start trace) {t base : ℕ}
    (hs : (trace.state t).status = .halted base) (n : ℕ) :
    trace.state (t + n) = trace.state t := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsn : (trace.state (t + n)).status = .halted base := by simpa [ih] using hs
      have heq := ((step_of_halted hsn).1 (h.2 (t + n))).2
      simpa only [Nat.add_succ] using heq.trans ih

/-- Charges stop exactly after successful halt; the finite prefix is stable. -/
theorem costThrough_add_of_halted {P : Program} {start : State P}
    {trace : Trace P} (h : LegalTrace P start trace) {t base : ℕ}
    (hs : (trace.state t).status = .halted base) (n : ℕ) :
    CostThrough P trace (t + n) = CostThrough P trace t := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsn : (trace.state (t + n)).status = .halted base := by
        rw [legalTrace_halted_state_add h hs n]
        exact hs
      have hcost := ((step_of_halted hsn).1 (h.2 (t + n))).1
      rw [Nat.add_succ, costThrough_succ, ih, hcost, Nat.add_zero]

#assert_trust kernel legalTrace_cost_eq
#assert_trust kernel costThrough_zero
#assert_trust kernel costThrough_succ
#assert_trust kernel charge_pos_of_running
#assert_trust kernel legalTrace_halted_state_add
#assert_trust kernel costThrough_add_of_halted
#print axioms costThrough_add_of_halted
end NLA.Proofs.TR04
