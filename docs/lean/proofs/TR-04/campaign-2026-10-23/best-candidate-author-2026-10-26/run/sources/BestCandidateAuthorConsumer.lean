import NLA.Proofs.TR04.MachineBestCandidateCallable
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace BestCandidateAuthorConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04
 theorem literal_standalone_minimum (p : BestCandidateData) (hp : 0 < p.count)
    (initialBest : ℝ) (scratch : BestCandidateScratch) (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p initialBest scratch) trace) :
    ∃ j < p.count,
      (trace.state (bestCandidateTime p)).status = .halted (p.store + j * p.entries) ∧
      (trace.state (bestCandidateTime p)).natural 5 = j ∧
      (trace.state (bestCandidateTime p)).natural 6 = p.store + j * p.entries ∧
      (trace.state (bestCandidateTime p)).real 3 =
        ∑ a ∈ Finset.range p.entries,
          (p.memory (p.baseA + a) - p.memory (p.store + j * p.entries + a))^2 ∧
      (∀ i < p.count,
        (∑ a ∈ Finset.range p.entries,
          (p.memory (p.baseA + a) - p.memory (p.store + j * p.entries + a))^2) ≤
        ∑ a ∈ Finset.range p.entries,
          (p.memory (p.baseA + a) - p.memory (p.store + i * p.entries + a))^2) ∧
      (trace.state (bestCandidateTime p)).memory = p.memory ∧
      CostThrough bestCandidateProgram trace (bestCandidateTime p) ≤
        50 * (p.count + p.entries + 1)^2 := bestCandidateProgram_run p hp initialBest scratch trace ht
 theorem literal_caller_minimum {Q : Program} (E : RoutineEmbedding bestCandidateProgram Q)
    (p : BestCandidateData) (hp : 0 < p.count) (initialBest : ℝ) (scratch : BestCandidateScratch)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (bestCandidateStart p initialBest scratch) (trace.state offset)) :
    ∃ j < p.count,
      (trace.state (offset + bestCandidateReturnTime p)).label = E.labels 25 ∧
      (trace.state (offset + bestCandidateReturnTime p)).status = .running ∧
      (trace.state (offset + bestCandidateReturnTime p)).natural (E.naturals 5) = j ∧
      (trace.state (offset + bestCandidateReturnTime p)).natural (E.naturals 6) =
        p.store + j * p.entries ∧
      (trace.state (offset + bestCandidateReturnTime p)).real (E.reals 3) = p.candidateError j ∧
      (∀ i < p.count, p.candidateError j ≤ p.candidateError i) ∧
      (trace.state (offset + bestCandidateReturnTime p)).memory = p.memory ∧
      CostThrough Q trace (offset + bestCandidateReturnTime p) ≤
        CostThrough Q trace offset + 50 * (p.count + p.entries + 1)^2 :=
  E.bestCandidate_value_at p hp initialBest scratch ht offset hs
 theorem zero_entries_actual_store (p : BestCandidateData) (hp : 0 < p.count)
    (hz : p.entries = 0) (initialBest : ℝ) (scratch : BestCandidateScratch)
    (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p initialBest scratch) trace) :
    (trace.state (bestCandidateTime p)).status = .halted p.store := by
  obtain ⟨j, _, hh, _⟩ := bestCandidateProgram_run p hp initialBest scratch trace ht
  simpa only [hz, Nat.mul_zero, Nat.add_zero] using hh
#assert_trust kernel literal_standalone_minimum
#assert_trust kernel literal_caller_minimum
#assert_trust kernel zero_entries_actual_store
#print axioms literal_standalone_minimum
#print axioms literal_caller_minimum
#print axioms zero_entries_actual_store
end BestCandidateAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData
#print axioms NLA.Proofs.TR04.BestCandidateData
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.candidateBase
#print axioms NLA.Proofs.TR04.BestCandidateData.candidateBase
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.candidateError
#print axioms NLA.Proofs.TR04.BestCandidateData.candidateError
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.MinimumSoFar
#print axioms NLA.Proofs.TR04.BestCandidateData.MinimumSoFar
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.minimum_take
#print axioms NLA.Proofs.TR04.BestCandidateData.minimum_take
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.minimum_keep
#print axioms NLA.Proofs.TR04.BestCandidateData.minimum_keep
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram
#print axioms NLA.Proofs.TR04.bestCandidateProgram
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters
#print axioms NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorLabels
#print axioms NLA.Proofs.TR04.bestCandidateErrorLabels
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorNaturals
#print axioms NLA.Proofs.TR04.bestCandidateErrorNaturals
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorReals
#print axioms NLA.Proofs.TR04.bestCandidateErrorReals
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorEmbedding
#print axioms NLA.Proofs.TR04.bestCandidateErrorEmbedding
#assert_trust kernel NLA.Proofs.TR04.BestCandidateScratch
#print axioms NLA.Proofs.TR04.BestCandidateScratch
#assert_trust kernel NLA.Proofs.TR04.bestCandidateState
#print axioms NLA.Proofs.TR04.bestCandidateState
#assert_trust kernel NLA.Proofs.TR04.bestCandidateLoopState
#print axioms NLA.Proofs.TR04.bestCandidateLoopState
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorState
#print axioms NLA.Proofs.TR04.bestCandidateErrorState
#assert_trust kernel NLA.Proofs.TR04.bestCandidateAfterError
#print axioms NLA.Proofs.TR04.bestCandidateAfterError
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_scalar
#print axioms NLA.Proofs.TR04.bestCandidateProgram_scalar
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_setup
#print axioms NLA.Proofs.TR04.bestCandidateProgram_setup
#assert_trust kernel NLA.Proofs.TR04.bestCandidate_error_relates
#print axioms NLA.Proofs.TR04.bestCandidate_error_relates
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_error
#print axioms NLA.Proofs.TR04.bestCandidateProgram_error
#assert_trust kernel NLA.Proofs.TR04.bestCandidateResultScratch
#print axioms NLA.Proofs.TR04.bestCandidateResultScratch
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_first
#print axioms NLA.Proofs.TR04.bestCandidateProgram_first
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_take
#print axioms NLA.Proofs.TR04.bestCandidateProgram_take
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_keep
#print axioms NLA.Proofs.TR04.bestCandidateProgram_keep
#assert_trust kernel NLA.Proofs.TR04.bestCandidateIterationTime
#print axioms NLA.Proofs.TR04.bestCandidateIterationTime
#assert_trust kernel NLA.Proofs.TR04.bestCandidateTime
#print axioms NLA.Proofs.TR04.bestCandidateTime
#assert_trust kernel NLA.Proofs.TR04.bestCandidateStart
#print axioms NLA.Proofs.TR04.bestCandidateStart
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_initial
#print axioms NLA.Proofs.TR04.bestCandidateProgram_initial
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_iteration
#print axioms NLA.Proofs.TR04.bestCandidateProgram_iteration
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_iterations
#print axioms NLA.Proofs.TR04.bestCandidateProgram_iterations
#assert_trust kernel NLA.Proofs.TR04.bestCandidateFinalState
#print axioms NLA.Proofs.TR04.bestCandidateFinalState
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_exit
#print axioms NLA.Proofs.TR04.bestCandidateProgram_exit
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_trace_result
#print axioms NLA.Proofs.TR04.bestCandidateProgram_trace_result
#assert_trust kernel NLA.Proofs.TR04.bestCandidateTime_le_polynomial
#print axioms NLA.Proofs.TR04.bestCandidateTime_le_polynomial
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_run
#print axioms NLA.Proofs.TR04.bestCandidateProgram_run
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_exists_trace
#print axioms NLA.Proofs.TR04.bestCandidateProgram_exists_trace
#assert_trust kernel NLA.Proofs.TR04.bestCandidateReturnTime
#print axioms NLA.Proofs.TR04.bestCandidateReturnTime
#assert_trust kernel NLA.Proofs.TR04.bestCandidateReturnState
#print axioms NLA.Proofs.TR04.bestCandidateReturnState
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_return_step
#print axioms NLA.Proofs.TR04.bestCandidateProgram_return_step
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_return
#print axioms NLA.Proofs.TR04.bestCandidateProgram_return
#assert_trust kernel NLA.Proofs.TR04.bestCandidateReturnTime_le_polynomial
#print axioms NLA.Proofs.TR04.bestCandidateReturnTime_le_polynomial
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_value_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_value_at
