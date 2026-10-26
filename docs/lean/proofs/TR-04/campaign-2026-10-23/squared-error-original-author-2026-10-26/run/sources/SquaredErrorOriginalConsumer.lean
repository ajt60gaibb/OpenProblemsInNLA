import NLA.Proofs.TR04.MachineSquaredErrorOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace SquaredErrorOriginalConsumer
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04
 theorem literal_squared_error (S : Shape) (memory : ℕ → ℝ) (baseA baseB : ℕ)
    (A B : Tensor S) (hA : ∀ x, memory (baseA + Offset S x) = A x)
    (hB : ∀ x, memory (baseB + Offset S x) = B x) :
    (∑ i ∈ Finset.range (∏ j, S.mode j),
      (memory (baseA + i) - memory (baseB + i))^2) = ∑ x : Index S, (A x - B x)^2 :=
  squaredErrorSum_eq_frobeniusSq S memory baseA baseB A B hA hB
 theorem literal_caller_error {Q : Program} (E : RoutineEmbedding squaredErrorProgram Q)
    (S : Shape) (r : Ranks S) (memory : ℕ → ℝ) (baseA baseB : ℕ) (A B : Tensor S)
    (hA : ∀ x, memory (baseA + Offset S x) = A x)
    (hB : ∀ x, memory (baseB + Offset S x) = B x)
    (accumulator scratchA scratchB : ℝ) {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (squaredErrorStart memory baseA baseB (DenseSize S)
      accumulator scratchA scratchB) (trace.state offset)) (ht : LegalTrace Q start trace) :
    (trace.state (offset + (9 * DenseSize S + 2))).label = E.labels 10 ∧
    (trace.state (offset + (9 * DenseSize S + 2))).real (E.reals 0) = ∑ x : Index S, (A x - B x)^2 ∧
    (trace.state (offset + (9 * DenseSize S + 2))).memory = memory ∧
    (trace.state (offset + (9 * DenseSize S + 2))).status = .running ∧
    CostThrough Q trace (offset + (9 * DenseSize S + 2)) ≤
      CostThrough Q trace offset + (9 * DenseSize S + 2) ∧
    CostThrough Q trace (offset + (9 * DenseSize S + 2)) ≤
      CostThrough Q trace offset + 11 * Size S r ∧
    (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →
      (trace.state (offset + (9 * DenseSize S + 2))).real j = (trace.state offset).real j) ∧
    (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
      (trace.state (offset + (9 * DenseSize S + 2))).natural j = (trace.state offset).natural j) :=
  E.squaredError_run_frobenius S r memory baseA baseB A B hA hB accumulator scratchA scratchB
    offset hs ht
#assert_trust kernel literal_squared_error
#assert_trust kernel literal_caller_error
#print axioms literal_squared_error
#print axioms literal_caller_error
end SquaredErrorOriginalConsumer
#assert_trust kernel NLA.Proofs.TR04.originalRadixIndexEquiv_eq_decode
#print axioms NLA.Proofs.TR04.originalRadixIndexEquiv_eq_decode
#assert_trust kernel NLA.Proofs.TR04.tensor_memory_cells_iff
#print axioms NLA.Proofs.TR04.tensor_memory_cells_iff
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum_eq_frobeniusSq
#print axioms NLA.Proofs.TR04.squaredErrorSum_eq_frobeniusSq
#assert_trust kernel NLA.Proofs.TR04.squaredErrorTime_shape_le_size
#print axioms NLA.Proofs.TR04.squaredErrorTime_shape_le_size
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_frobenius
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_frobenius
