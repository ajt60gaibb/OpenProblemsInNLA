import NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace MatrixMultiplyAuthorConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04
 theorem actual_finite_strided_program (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) :
    (∃ trace, LegalTrace matrixMultiplyProgram (matrixMultiplyStart p) trace) ∧
    ∀ trace, LegalTrace matrixMultiplyProgram (matrixMultiplyStart p) trace →
      (trace.state (matrixMultiplyTime p)).status = .halted p.dBase ∧
      (∀ (i : Fin p.rows) (j : Fin p.cols),
        (trace.state (matrixMultiplyTime p)).memory (p.dBase + i.val * p.cols + j.val) =
        ∑ a : Fin p.inner,
          p.memory (p.bBase + i.val * p.bRowStride + a.val * p.bColStride) *
          p.memory (p.cBase + a.val * p.cRowStride + j.val * p.cColStride)) ∧
      (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
        (trace.state (matrixMultiplyTime p)).memory address = p.memory address) ∧
      CostThrough matrixMultiplyProgram trace (matrixMultiplyTime p) ≤
        17 * (p.rows + p.inner + p.cols + 1) ^ 3 := by
  refine ⟨matrixMultiplyProgram_exists_trace p, ?_⟩
  intro trace ht
  obtain ⟨hh, hp, ho, hc⟩ := matrixMultiplyProgram_run p h trace ht
  refine ⟨hh, ?_, ho, hc⟩
  intro i j
  have he := congrArg (fun M : Matrix (Fin p.rows) (Fin p.cols) ℝ => M i j) hp
  simpa only [readMatrix, Matrix.mul_apply, MatrixMultiplyData.leftMatrix,
    MatrixMultiplyData.rightMatrix, MatrixMultiplyData.bAddress,
    MatrixMultiplyData.cAddress] using he
#assert_trust kernel actual_finite_strided_program
#print axioms actual_finite_strided_program
end MatrixMultiplyAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData
#print axioms NLA.Proofs.TR04.MatrixMultiplyData
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.bAddress
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.bAddress
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.cAddress
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.cAddress
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.productMatrix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.productMatrix
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.partialProduct
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.partialProduct
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_zero
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_zero
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_succ
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_succ
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.InputsOutsideOutput
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.InputsOutsideOutput
#assert_trust kernel NLA.Proofs.TR04.prefixMemory
#print axioms NLA.Proofs.TR04.prefixMemory
#assert_trust kernel NLA.Proofs.TR04.prefixMemory_zero
#print axioms NLA.Proofs.TR04.prefixMemory_zero
#assert_trust kernel NLA.Proofs.TR04.prefixMemory_outside
#print axioms NLA.Proofs.TR04.prefixMemory_outside
#assert_trust kernel NLA.Proofs.TR04.prefixMemory_update
#print axioms NLA.Proofs.TR04.prefixMemory_update
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_source
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_source
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_b
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_b
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_c
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_c
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_update
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_update
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_read
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_read
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyScratch
#print axioms NLA.Proofs.TR04.MatrixMultiplyScratch
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyState
#print axioms NLA.Proofs.TR04.matrixMultiplyState
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyCellState
#print axioms NLA.Proofs.TR04.matrixMultiplyCellState
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyInnerState
#print axioms NLA.Proofs.TR04.matrixMultiplyInnerState
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyRowState
#print axioms NLA.Proofs.TR04.matrixMultiplyRowState
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_scalar
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_scalar
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cell_setup
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cell_setup
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_inner_eight
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_inner_eight
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_inner_iterations
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_inner_iterations
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cell_exit
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cell_exit
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyCellTime
#print axioms NLA.Proofs.TR04.matrixMultiplyCellTime
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyRowTime
#print axioms NLA.Proofs.TR04.matrixMultiplyRowTime
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyTime
#print axioms NLA.Proofs.TR04.matrixMultiplyTime
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyStart
#print axioms NLA.Proofs.TR04.matrixMultiplyStart
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyStart_eq_row
#print axioms NLA.Proofs.TR04.matrixMultiplyStart_eq_row
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cell
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cell
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cells
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cells
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_row_setup
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_row_setup
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_row_exit
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_row_exit
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_row
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_row
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_rows
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_rows
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyFinalState
#print axioms NLA.Proofs.TR04.matrixMultiplyFinalState
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_exit
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_exit
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_trace_result
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_trace_result
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_trace_product
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_trace_product
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyTime_le_cubic
#print axioms NLA.Proofs.TR04.matrixMultiplyTime_le_cubic
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_run
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_run
