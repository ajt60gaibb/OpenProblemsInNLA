import NLA.Proofs.TR04.MachineSquaredErrorTrace
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
open NLA.Computation.SVDMachine NLA.Proofs.TR04
namespace SquaredErrorExactConsumer
theorem standalone (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) (trace : Trace squaredErrorProgram)
    (htrace : LegalTrace squaredErrorProgram
      (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) trace) :
    (trace.state (9 * count + 3)).status = .halted 0 ∧
      (trace.state (9 * count + 3)).real 0 =
        ∑ i ∈ Finset.range count, (memory (baseA + i) - memory (baseB + i))^2 ∧
      (trace.state (9 * count + 3)).memory = memory ∧
      CostThrough squaredErrorProgram trace (9 * count + 3) ≤ 9 * count + 3 := by
  obtain ⟨hs, hr, hm⟩ := squaredErrorProgram_trace_result memory baseA baseB count
    accumulator scratchA scratchB trace htrace
  exact ⟨hs, hr, hm, squaredErrorProgram_trace_cost memory baseA baseB count
    accumulator scratchA scratchB trace htrace⟩
#assert_trust kernel SquaredErrorExactConsumer.standalone
theorem embedded {Q : Program} (E : RoutineEmbedding squaredErrorProgram Q)
    (memory : ℕ → ℝ) (baseA baseB count : ℕ) (accumulator scratchA scratchB : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    (trace.state (offset + (9 * count + 2))).label = E.labels 10 ∧
      (trace.state (offset + (9 * count + 2))).real (E.reals 0) =
        ∑ i ∈ Finset.range count, (memory (baseA + i) - memory (baseB + i))^2 ∧
      (trace.state (offset + (9 * count + 2))).memory = memory ∧
      (trace.state (offset + (9 * count + 2))).status = .running ∧
      CostThrough Q trace (offset + (9 * count + 2)) ≤
        CostThrough Q trace offset + (9 * count + 2) :=
  E.squaredError_run_value memory baseA baseB count accumulator scratchA scratchB offset hs ht
#assert_trust kernel SquaredErrorExactConsumer.embedded
end SquaredErrorExactConsumer

#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram
#print axioms NLA.Proofs.TR04.squaredErrorProgram
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum
#print axioms NLA.Proofs.TR04.squaredErrorSum
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum_zero
#print axioms NLA.Proofs.TR04.squaredErrorSum_zero
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum_succ
#print axioms NLA.Proofs.TR04.squaredErrorSum_succ
#assert_trust kernel NLA.Proofs.TR04.squaredErrorLoopState
#print axioms NLA.Proofs.TR04.squaredErrorLoopState
#assert_trust kernel NLA.Proofs.TR04.squaredErrorStart
#print axioms NLA.Proofs.TR04.squaredErrorStart
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_scalar
#print axioms NLA.Proofs.TR04.squaredErrorProgram_scalar
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_initialize
#print axioms NLA.Proofs.TR04.squaredErrorProgram_initialize
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nine_steps
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nine_steps
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_iterations
#print axioms NLA.Proofs.TR04.squaredErrorProgram_iterations
#assert_trust kernel NLA.Proofs.TR04.squaredErrorFinalState
#print axioms NLA.Proofs.TR04.squaredErrorFinalState
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_exit
#print axioms NLA.Proofs.TR04.squaredErrorProgram_exit
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_finish
#print axioms NLA.Proofs.TR04.squaredErrorProgram_finish
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_trace_result
#print axioms NLA.Proofs.TR04.squaredErrorProgram_trace_result
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_trace_cost
#print axioms NLA.Proofs.TR04.squaredErrorProgram_trace_cost
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nohalt_phase
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nohalt_phase
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nohalt_loop_prefix
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nohalt_loop_prefix
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nohalt_prefix
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nohalt_prefix
#assert_trust kernel NLA.Proofs.TR04.squaredErrorReturnState
#print axioms NLA.Proofs.TR04.squaredErrorReturnState
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_return
#print axioms NLA.Proofs.TR04.squaredErrorProgram_return
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_value
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_value
