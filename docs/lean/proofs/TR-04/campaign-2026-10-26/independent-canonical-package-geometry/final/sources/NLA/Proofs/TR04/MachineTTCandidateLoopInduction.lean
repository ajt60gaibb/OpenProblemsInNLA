import NLA.Proofs.TR04.MachineTTProgramFacts
import NLA.Proofs.TR04.MachineScalarRoutines

/-! Induction over actual finite candidate-loop continuations. A continuation
proof carries the invariant, real instruction elapsed time, and charged cost;
the program receives no invariant or continuation as data. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem ttCandidateLoop_induction (trace : Trace ttProgram) (K budget : ℕ)
    (I : State ttProgram → Prop)
    (step : ∀ offset : ℕ,I (trace.state offset) →
      (trace.state offset).label=189 → (trace.state offset).status=.running →
      (trace.state offset).natural 76<K →
      ∃ elapsed : ℕ,elapsed≤budget ∧ I (trace.state (offset+elapsed)) ∧
        (trace.state (offset+elapsed)).label=189 ∧
        (trace.state (offset+elapsed)).status=.running ∧
        (trace.state (offset+elapsed)).natural 76=(trace.state offset).natural 76+1 ∧
        CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+budget)
    (offset : ℕ) (hi : I (trace.state offset))
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hj : (trace.state offset).natural 76=0) :
    ∃ elapsed : ℕ,elapsed≤K*budget ∧ I (trace.state (offset+elapsed)) ∧
      (trace.state (offset+elapsed)).label=189 ∧
      (trace.state (offset+elapsed)).status=.running ∧
      (trace.state (offset+elapsed)).natural 76=K ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+K*budget := by
  have run : ∀ j : ℕ,j≤K →
      ∃ elapsed : ℕ,elapsed≤j*budget ∧ I (trace.state (offset+elapsed)) ∧
        (trace.state (offset+elapsed)).label=189 ∧
        (trace.state (offset+elapsed)).status=.running ∧
        (trace.state (offset+elapsed)).natural 76=j ∧
        CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+j*budget := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0,by omega,?_,?_,?_,?_,?_⟩
      · simpa only [Nat.add_zero] using hi
      · simpa only [Nat.add_zero] using hl
      · simpa only [Nat.add_zero] using hs
      · simpa only [Nat.add_zero] using hj
      · simp only [Nat.add_zero,Nat.zero_mul,le_refl]
    | succ j ih =>
      intro hbound
      obtain ⟨e,he,hi',hl',hs',hj',hc⟩ := ih (by omega)
      obtain ⟨e',he',hi'',hl'',hs'',hj'',hc'⟩ := step (offset+e) hi' hl' hs' (by rw [hj'];omega)
      have htime : offset+e+e'=offset+(e+e') := by omega
      rw [htime] at hi'' hl'' hs'' hj'' hc'
      refine ⟨e+e',?_,hi'',hl'',hs'',?_,?_⟩
      · rw [Nat.succ_mul]
        omega
      · omega
      · rw [Nat.succ_mul]
        omega
  exact run K le_rfl

#assert_trust kernel ttCandidateLoop_induction
#print axioms ttCandidateLoop_induction
end NLA.Proofs.TR04
