import NLA.Proofs.TR04.MachineScalarRoutines

/-! Actual trace suffixes and charged-cost composition. These permit the fixed
caller program to run verified finite instruction blocks one after another. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def shiftedTrace {P : Program} (trace : Trace P) (offset : ℕ) : Trace P where
  state k := trace.state (offset + k)
  cost k := trace.cost (offset + k)

theorem legalTrace_shift {P : Program} {start : State P} {trace : Trace P}
    (h : LegalTrace P start trace) (offset : ℕ) :
    LegalTrace P (trace.state offset) (shiftedTrace trace offset) := by
  refine ⟨by simp [shiftedTrace],?_⟩
  intro k
  simpa only [shiftedTrace,Nat.add_assoc] using h.2 (offset + k)

theorem costThrough_shift {P : Program} (trace : Trace P) (offset n : ℕ) :
    CostThrough P trace (offset + n) =
      CostThrough P trace offset + CostThrough P (shiftedTrace trace offset) n := by
  simp only [CostThrough,Finset.sum_range_add,shiftedTrace,Nat.add_comm]

theorem costThrough_compose_le {P : Program} {trace : Trace P} {offset n a b : ℕ}
    (hfirst : CostThrough P trace offset ≤ a)
    (hsecond : CostThrough P (shiftedTrace trace offset) n ≤ b) :
    CostThrough P trace (offset + n) ≤ a + b := by
  rw [costThrough_shift]
  omega

/-- A copied dense block may occur at any actual caller trace time. -/
theorem RoutineEmbedding.copy_run_at {Q : Program} (E : RoutineEmbedding copyProgram Q)
    (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hd : DisjointBlocks src count dst count) {start : State Q} {trace : Trace Q}
    (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (copyLoopState memory src dst count 0 scratch) (trace.state offset)) :
    ∃ value : ℝ, E.Relates (copyReturnState memory src dst count value)
      (trace.state (offset + (6 * count + 1))) ∧
      CostThrough Q trace (offset + (6 * count + 1)) ≤ CostThrough Q trace offset + (6 * count + 1) := by
  obtain ⟨⟨value,hr⟩,hc⟩ := E.copy_run memory src dst count scratch hd hs (legalTrace_shift ht offset)
  refine ⟨value,hr,?_⟩
  exact costThrough_compose_le le_rfl hc

/-- Header decoding likewise composes using actual suffix charges. -/
theorem RoutineEmbedding.decodeNatural_run_at {Q : Program}
    (E : RoutineEmbedding decodeNaturalProgram Q) (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (decodeNaturalLoopState memory base count 0 scratch) (trace.state offset)) :
    E.Relates (decodeNaturalReturnState memory base count)
      (trace.state (offset + (3 * count + 2))) ∧
      CostThrough Q trace (offset + (3 * count + 2)) ≤ CostThrough Q trace offset + (3 * count + 2) := by
  obtain ⟨hr,hc⟩ := E.decodeNatural_run memory base count scratch hs (legalTrace_shift ht offset)
  exact ⟨hr,costThrough_compose_le le_rfl hc⟩

#assert_trust kernel shiftedTrace
#assert_trust kernel legalTrace_shift
#assert_trust kernel costThrough_shift
#assert_trust kernel costThrough_compose_le
#assert_trust kernel RoutineEmbedding.copy_run_at
#assert_trust kernel RoutineEmbedding.decodeNatural_run_at
#print axioms RoutineEmbedding.decodeNatural_run_at
end NLA.Proofs.TR04
