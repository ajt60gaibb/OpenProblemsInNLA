import NLA.Proofs.TR04.MachineTraceBounds

/-! Deterministic scalar prefixes inside the actual nondeterministic SVD machine.
Every premise refers to the fixed instruction syntax along an actual finite
ordinaryStep path; there is no alternate evaluator or freely assigned cost. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Fieldwise equality of actual machine states. -/
@[ext] theorem machineState_ext {P : Program} {s t : State P}
    (hlabel : s.label = t.label) (hreal : s.real = t.real)
    (hnatural : s.natural = t.natural) (hmemory : s.memory = t.memory)
    (hstatus : s.status = t.status) : s = t := by
  cases s
  cases t
  cases hlabel
  cases hreal
  cases hnatural
  cases hmemory
  cases hstatus
  rfl

def instructionIsSVD {labels reals naturals constants : ℕ} :
    Instruction labels reals naturals constants → Bool
  | .svd _ _ _ _ _ _ _ => true
  | _ => false

/-- Scalar instructions have their literal deterministic transition, including
failing arithmetic guards. Already halted/failed states remain absorbing. -/
theorem step_iff_ordinary_of_scalar {P : Program} {s t : State P} {cost : ℕ}
    (hscalar : s.status = .running → instructionIsSVD (P.code s.label) = false) :
    Step P s t cost ↔ cost = charge P s ∧ t = ordinaryStep P s := by
  cases hs : s.status with
  | halted base => simp [Step, ordinaryStep, hs]
  | failed => simp [Step, ordinaryStep, hs]
  | running =>
      have hcode := hscalar hs
      cases hi : P.code s.label <;> simp_all [Step, instructionIsSVD]

/-- A finite literal scalar-instruction path is forced in every legal trace,
even though future SVD responses may be arbitrary. -/
theorem legalTrace_scalar_prefix {P : Program} {start : State P} {trace : Trace P}
    (htrace : LegalTrace P start trace) (n : ℕ)
    (hscalar : ∀ k < n, ((ordinaryStep P)^[k] start).status = .running →
      instructionIsSVD (P.code ((ordinaryStep P)^[k] start).label) = false) :
    trace.state n = (ordinaryStep P)^[n] start := by
  induction n with
  | zero => simpa using htrace.1
  | succ n ih =>
      have hprefix : ∀ k < n, ((ordinaryStep P)^[k] start).status = .running →
          instructionIsSVD (P.code ((ordinaryStep P)^[k] start).label) = false :=
        fun k hk => hscalar k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have heq := ih hprefix
      have hsc : (trace.state n).status = .running →
          instructionIsSVD (P.code (trace.state n).label) = false := by
        simpa only [heq] using hscalar n (Nat.lt_succ_self n)
      have hnext := ((step_iff_ordinary_of_scalar hsc).1 (htrace.2 n)).2
      rw [hnext, heq, Function.iterate_succ_apply']

/-- Exact charged-prefix cost for a scalar block, rather than an assumed
operation-count field or an estimate detached from the transition trace. -/
theorem costThrough_scalar_prefix {P : Program} {start : State P} {trace : Trace P}
    (htrace : LegalTrace P start trace) (n : ℕ)
    (hscalar : ∀ k < n, ((ordinaryStep P)^[k] start).status = .running →
      instructionIsSVD (P.code ((ordinaryStep P)^[k] start).label) = false) :
    CostThrough P trace n = ∑ k ∈ Finset.range n, charge P ((ordinaryStep P)^[k] start) := by
  unfold CostThrough
  apply Finset.sum_congr rfl
  intro k hk
  rw [legalTrace_cost_eq htrace k]
  have hk' := Finset.mem_range.mp hk
  rw [legalTrace_scalar_prefix htrace k (fun j hj => hscalar j (Nat.lt_trans hj hk'))]

/-- Each actual scalar instruction costs one while running and zero after stop. -/
theorem charge_le_one_of_scalar {P : Program} {s : State P}
    (hscalar : s.status = .running → instructionIsSVD (P.code s.label) = false) :
    charge P s ≤ 1 := by
  cases hs : s.status with
  | halted base => simp [charge, hs]
  | failed => simp [charge, hs]
  | running =>
      have hcode := hscalar hs
      cases hi : P.code s.label <;> simp_all [charge, instructionIsSVD]

/-- Uniform actual charged-prefix bound for a program containing scalar instructions. -/
theorem costThrough_le_scalar {P : Program} {start : State P} {trace : Trace P}
    (htrace : LegalTrace P start trace)
    (hscalar : ∀ s : State P, instructionIsSVD (P.code s.label) = false) (n : ℕ) :
    CostThrough P trace n ≤ n := by
  unfold CostThrough
  calc
    ∑ k ∈ Finset.range n, trace.cost k ≤ ∑ _k ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro k _
      rw [legalTrace_cost_eq htrace k]
      exact charge_le_one_of_scalar (fun _ => hscalar _)
    _ = n := by simp

#assert_trust kernel charge_le_one_of_scalar
#assert_trust kernel costThrough_le_scalar
#assert_trust kernel machineState_ext
#assert_trust kernel instructionIsSVD
#assert_trust kernel step_iff_ordinary_of_scalar
#assert_trust kernel legalTrace_scalar_prefix
#assert_trust kernel costThrough_scalar_prefix
#print axioms costThrough_scalar_prefix
end NLA.Proofs.TR04
