import NLA.Proofs.TR04.MachineBestCandidateCorrectness
import NLA.Proofs.TR04.MachineNoEarlyHalt

/-! The selector is callable before its local halt. An actual caller reaches
its mapped continuation with the winning index/base/error and unchanged memory. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def bestCandidateReturnTime (p : BestCandidateData) : ℕ :=
  bestCandidateIterationTime p * p.count + 3

def bestCandidateReturnState (p : BestCandidateData) (winner : ℕ) (error : ℝ)
    (scratch : BestCandidateScratch) : State bestCandidateProgram :=
  { bestCandidateLoopState p p.count winner error scratch with label := 25 }

theorem bestCandidateProgram_return_step (p : BestCandidateData) (winner : ℕ) (error : ℝ)
    (scratch : BestCandidateScratch) :
    ordinaryStep bestCandidateProgram (bestCandidateLoopState p p.count winner error scratch) =
      bestCandidateReturnState p winner error scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, ordinaryStep, bestCandidateProgram, bestCandidateLoopState,
    bestCandidateReturnState, bestCandidateState]

theorem bestCandidateProgram_return (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) :
    ∃ winner < p.count, ∃ result : BestCandidateScratch,
      (ordinaryStep bestCandidateProgram)^[bestCandidateReturnTime p]
        (bestCandidateStart p value scratch) =
          bestCandidateReturnState p winner (p.candidateError winner) result ∧
      ∀ i < p.count, p.candidateError winner ≤ p.candidateError i := by
  obtain ⟨winner, error, result, hr, hmin⟩ := bestCandidateProgram_iterations p value scratch
    p.count le_rfl
  obtain ⟨hw, he, hleast⟩ := hmin.resolve_left (by omega)
  rw [he] at hr hleast
  refine ⟨winner, hw, result, ?_, hleast⟩
  have htime : bestCandidateReturnTime p = 1 + (bestCandidateIterationTime p * p.count + 2) := by
    unfold bestCandidateReturnTime
    omega
  rw [htime, Function.iterate_add_apply, Function.iterate_add_apply, bestCandidateProgram_initial, hr]
  exact bestCandidateProgram_return_step p winner (p.candidateError winner) result

theorem bestCandidateReturnTime_le_polynomial (p : BestCandidateData) :
    bestCandidateReturnTime p ≤ 50 * (p.count + p.entries + 1)^2 := by
  have ht := bestCandidateTime_le_polynomial p
  unfold bestCandidateReturnTime bestCandidateTime at *
  omega

/-- Every actual caller reaches the continuation with the actual finite
minimum. The incoming best-error register is arbitrary and is overwritten
by the first actual candidate. Outside-frame caller registers are preserved. -/
theorem RoutineEmbedding.bestCandidate_run_at {Q : Program}
    (E : RoutineEmbedding bestCandidateProgram Q) (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) {start : State Q} {trace : Trace Q}
    (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (bestCandidateStart p value scratch) (trace.state offset)) :
    ∃ winner < p.count, ∃ result : BestCandidateScratch,
      E.Relates (bestCandidateReturnState p winner (p.candidateError winner) result)
        (trace.state (offset + bestCandidateReturnTime p)) ∧
      (∀ i < p.count, p.candidateError winner ≤ p.candidateError i) ∧
      CostThrough Q trace (offset + bestCandidateReturnTime p) ≤
        CostThrough Q trace offset + bestCandidateReturnTime p ∧
      CostThrough Q trace (offset + bestCandidateReturnTime p) ≤
        CostThrough Q trace offset + 50 * (p.count + p.entries + 1)^2 ∧
      (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state (offset + bestCandidateReturnTime p)).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state (offset + bestCandidateReturnTime p)).natural j =
          (trace.state offset).natural j) := by
  obtain ⟨winner, hw, result, hr, hmin⟩ := bestCandidateProgram_return p hp value scratch
  have hfinal : ((ordinaryStep bestCandidateProgram)^[bestCandidateReturnTime p]
      (bestCandidateStart p value scratch)).status = .running := by rw [hr]; rfl
  have hno := ordinary_nohalt_prefix_of_running _ _ hfinal
  have hscalar : ∀ k < bestCandidateReturnTime p,
      instructionIsSVD (bestCandidateProgram.code
        ((ordinaryStep bestCandidateProgram)^[k] (bestCandidateStart p value scratch)).label) =
        false := fun _ _ => bestCandidateProgram_scalar _
  have htail := legalTrace_shift ht offset
  have hrel := E.scalar_trace_prefix _ hs htail _ hno hscalar
  have hcost := E.scalar_trace_cost_le _ hs htail _ hno hscalar
  have hc : CostThrough Q trace (offset + bestCandidateReturnTime p) ≤
      CostThrough Q trace offset + bestCandidateReturnTime p :=
    costThrough_compose_le le_rfl hcost
  rw [hr] at hrel
  refine ⟨winner, hw, result, hrel, hmin, hc, ?_, ?_, ?_⟩
  · exact hc.trans (Nat.add_le_add_left (bestCandidateReturnTime_le_polynomial p) _)
  · intro j hj
    exact E.scalar_trace_real_outside _ hs htail _ hno hscalar j hj
  · intro j hj
    exact E.scalar_trace_natural_outside _ hs htail _ hno hscalar j hj

/-- Direct literal caller fields at the selected candidate's return point. -/
theorem RoutineEmbedding.bestCandidate_value_at {Q : Program}
    (E : RoutineEmbedding bestCandidateProgram Q) (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) {start : State Q} {trace : Trace Q}
    (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (bestCandidateStart p value scratch) (trace.state offset)) :
    ∃ winner < p.count,
      (trace.state (offset + bestCandidateReturnTime p)).label = E.labels 25 ∧
      (trace.state (offset + bestCandidateReturnTime p)).status = .running ∧
      (trace.state (offset + bestCandidateReturnTime p)).natural (E.naturals 5) = winner ∧
      (trace.state (offset + bestCandidateReturnTime p)).natural (E.naturals 6) =
        p.store + winner * p.entries ∧
      (trace.state (offset + bestCandidateReturnTime p)).real (E.reals 3) = p.candidateError winner ∧
      (∀ i < p.count, p.candidateError winner ≤ p.candidateError i) ∧
      (trace.state (offset + bestCandidateReturnTime p)).memory = p.memory ∧
      CostThrough Q trace (offset + bestCandidateReturnTime p) ≤
        CostThrough Q trace offset + 50 * (p.count + p.entries + 1)^2 := by
  obtain ⟨winner, hw, result, hr, hmin, _, hc, _, _⟩ :=
    E.bestCandidate_run_at p hp value scratch ht offset hs
  exact ⟨winner, hw, hr.label, hr.status, hr.natural_apply 5, hr.natural_apply 6,
    hr.real_apply 3, hmin, hr.memory, hc⟩

#assert_trust kernel bestCandidateProgram_return
#assert_trust kernel RoutineEmbedding.bestCandidate_run_at
#assert_trust kernel RoutineEmbedding.bestCandidate_value_at
#print axioms RoutineEmbedding.bestCandidate_run_at
#print axioms RoutineEmbedding.bestCandidate_value_at
end NLA.Proofs.TR04
