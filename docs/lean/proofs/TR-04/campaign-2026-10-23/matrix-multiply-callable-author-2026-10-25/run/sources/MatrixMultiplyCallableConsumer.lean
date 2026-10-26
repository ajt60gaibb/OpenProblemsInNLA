import NLA.Proofs.TR04.MachineMatrixMultiplyCallable
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace MatrixMultiplyCallableConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04
 theorem arbitrary_caller_actual_fields {Q : Program}
    (E : RoutineEmbedding matrixMultiplyProgram Q) (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState p 0 scratch) (trace.state offset)) :
    (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).label = E.labels 21 ∧
    (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).status = .running ∧
    readMatrix (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).memory
      p.rows p.cols p.dBase = p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).memory address = p.memory address) ∧
    CostThrough Q trace (offset + (matrixMultiplyRowTime p * p.rows + 1)) ≤
      CostThrough Q trace offset + 17 * (p.rows + p.inner + p.cols + 1) ^ 3 ∧
    (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →
      (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).real j =
        (trace.state offset).real j) ∧
    (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
      (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).natural j =
        (trace.state offset).natural j) :=
  E.matrixMultiply_product_at p h scratch ht offset hs
#assert_trust kernel arbitrary_caller_actual_fields
#print axioms arbitrary_caller_actual_fields
end MatrixMultiplyCallableConsumer
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnTime
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnTime
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnState
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnState
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_return_step
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_return_step
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_return
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_return
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnState_product
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnState_product
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnTime_le_cubic
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnTime_le_cubic
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_nohalt
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_nohalt
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_product_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_product_at
