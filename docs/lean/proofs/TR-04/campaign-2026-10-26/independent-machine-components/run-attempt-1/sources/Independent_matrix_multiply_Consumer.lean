import NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness

set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#assert_kind " n:ident expected:str : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some info := (← getEnv).find? decl | throwErrorAt n "missing actual constant"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt n "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {decl} {expected.getString}"
#assert_kind NLA.Computation.SVDMachine.Instruction "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Instruction
#print axioms NLA.Computation.SVDMachine.Instruction
#assert_kind NLA.Computation.SVDMachine.Program "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Program
#print axioms NLA.Computation.SVDMachine.Program
#assert_kind NLA.Computation.SVDMachine.Status "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Status
#print axioms NLA.Computation.SVDMachine.Status
#assert_kind NLA.Computation.SVDMachine.State "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.State
#print axioms NLA.Computation.SVDMachine.State
#assert_kind NLA.Computation.SVDMachine.initial "definition"
#assert_trust kernel NLA.Computation.SVDMachine.initial
#print axioms NLA.Computation.SVDMachine.initial
#assert_kind NLA.Computation.SVDMachine.ordinaryStep "definition"
#assert_trust kernel NLA.Computation.SVDMachine.ordinaryStep
#print axioms NLA.Computation.SVDMachine.ordinaryStep
#assert_kind NLA.Computation.SVDMachine.ValidSVD "definition"
#assert_trust kernel NLA.Computation.SVDMachine.ValidSVD
#print axioms NLA.Computation.SVDMachine.ValidSVD
#assert_kind NLA.Computation.SVDMachine.DisjointBlocks "definition"
#assert_trust kernel NLA.Computation.SVDMachine.DisjointBlocks
#print axioms NLA.Computation.SVDMachine.DisjointBlocks
#assert_kind NLA.Computation.SVDMachine.OutputBlocksDisjoint "definition"
#assert_trust kernel NLA.Computation.SVDMachine.OutputBlocksDisjoint
#print axioms NLA.Computation.SVDMachine.OutputBlocksDisjoint
#assert_kind NLA.Computation.SVDMachine.matrixCell "definition"
#assert_trust kernel NLA.Computation.SVDMachine.matrixCell
#print axioms NLA.Computation.SVDMachine.matrixCell
#assert_kind NLA.Computation.SVDMachine.readMatrix "definition"
#assert_trust kernel NLA.Computation.SVDMachine.readMatrix
#print axioms NLA.Computation.SVDMachine.readMatrix
#assert_kind NLA.Computation.SVDMachine.writeSVD "definition"
#assert_trust kernel NLA.Computation.SVDMachine.writeSVD
#print axioms NLA.Computation.SVDMachine.writeSVD
#assert_kind NLA.Computation.SVDMachine.charge "definition"
#assert_trust kernel NLA.Computation.SVDMachine.charge
#print axioms NLA.Computation.SVDMachine.charge
#assert_kind NLA.Computation.SVDMachine.Step "definition"
#assert_trust kernel NLA.Computation.SVDMachine.Step
#print axioms NLA.Computation.SVDMachine.Step
#assert_kind NLA.Computation.SVDMachine.Trace "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Trace
#print axioms NLA.Computation.SVDMachine.Trace
#assert_kind NLA.Computation.SVDMachine.LegalTrace "definition"
#assert_trust kernel NLA.Computation.SVDMachine.LegalTrace
#print axioms NLA.Computation.SVDMachine.LegalTrace
#assert_kind NLA.Computation.SVDMachine.CostThrough "definition"
#assert_trust kernel NLA.Computation.SVDMachine.CostThrough
#print axioms NLA.Computation.SVDMachine.CostThrough
#assert_kind NLA.Proofs.TR04.matrix_offset_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrix_offset_lt
#print axioms NLA.Proofs.TR04.matrix_offset_lt
#assert_kind NLA.Proofs.TR04.matrixCell_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixCell_entry
#print axioms NLA.Proofs.TR04.matrixCell_entry
#assert_kind NLA.Proofs.TR04.disjointBlocks_not_mem_right "theorem"
#assert_trust kernel NLA.Proofs.TR04.disjointBlocks_not_mem_right
#print axioms NLA.Proofs.TR04.disjointBlocks_not_mem_right
#assert_kind NLA.Proofs.TR04.disjointBlocks_not_mem_left "theorem"
#assert_trust kernel NLA.Proofs.TR04.disjointBlocks_not_mem_left
#print axioms NLA.Proofs.TR04.disjointBlocks_not_mem_left
#assert_kind NLA.Proofs.TR04.writeSVD_u_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_u_entry
#print axioms NLA.Proofs.TR04.writeSVD_u_entry
#assert_kind NLA.Proofs.TR04.readMatrix_writeSVD_u "theorem"
#assert_trust kernel NLA.Proofs.TR04.readMatrix_writeSVD_u
#print axioms NLA.Proofs.TR04.readMatrix_writeSVD_u
#assert_kind NLA.Proofs.TR04.writeSVD_sigma_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_sigma_entry
#print axioms NLA.Proofs.TR04.writeSVD_sigma_entry
#assert_kind NLA.Proofs.TR04.writeSVD_v_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_v_entry
#print axioms NLA.Proofs.TR04.writeSVD_v_entry
#assert_kind NLA.Proofs.TR04.readMatrix_writeSVD_v "theorem"
#assert_trust kernel NLA.Proofs.TR04.readMatrix_writeSVD_v
#print axioms NLA.Proofs.TR04.readMatrix_writeSVD_v
#assert_kind NLA.Proofs.TR04.writeSVD_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_outside
#print axioms NLA.Proofs.TR04.writeSVD_outside
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData "inductive"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData
#print axioms NLA.Proofs.TR04.MatrixMultiplyData
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.bAddress "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.bAddress
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.bAddress
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.cAddress "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.cAddress
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.cAddress
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.productMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.productMatrix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.productMatrix
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.partialProduct "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.partialProduct
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.partialProduct
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_zero
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_zero
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_succ
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_succ
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.InputsOutsideOutput "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.InputsOutsideOutput
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.InputsOutsideOutput
#assert_kind NLA.Proofs.TR04.prefixMemory "definition"
#assert_trust kernel NLA.Proofs.TR04.prefixMemory
#print axioms NLA.Proofs.TR04.prefixMemory
#assert_kind NLA.Proofs.TR04.prefixMemory_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.prefixMemory_zero
#print axioms NLA.Proofs.TR04.prefixMemory_zero
#assert_kind NLA.Proofs.TR04.prefixMemory_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.prefixMemory_outside
#print axioms NLA.Proofs.TR04.prefixMemory_outside
#assert_kind NLA.Proofs.TR04.prefixMemory_update "theorem"
#assert_trust kernel NLA.Proofs.TR04.prefixMemory_update
#print axioms NLA.Proofs.TR04.prefixMemory_update
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix "definition"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_source "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_source
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_source
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_b "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_b
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_b
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_c "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_c
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_c
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_update "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_update
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_update
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_read "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_read
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_read
#assert_kind NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput "theorem"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput
#print axioms NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput
#assert_kind NLA.Computation.TensorTrainApproximation.Shape "inductive"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Shape
#print axioms NLA.Computation.TensorTrainApproximation.Shape
#assert_kind NLA.Computation.TensorTrainApproximation.Index "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Index
#print axioms NLA.Computation.TensorTrainApproximation.Index
#assert_kind NLA.Computation.TensorTrainApproximation.Tensor "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Tensor
#print axioms NLA.Computation.TensorTrainApproximation.Tensor
#assert_kind NLA.Computation.TensorTrainApproximation.Cut "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Cut
#print axioms NLA.Computation.TensorTrainApproximation.Cut
#assert_kind NLA.Computation.TensorTrainApproximation.Ranks "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Ranks
#print axioms NLA.Computation.TensorTrainApproximation.Ranks
#assert_kind NLA.Computation.TensorTrainApproximation.RowIndex "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.RowIndex
#print axioms NLA.Computation.TensorTrainApproximation.RowIndex
#assert_kind NLA.Computation.TensorTrainApproximation.ColIndex "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.ColIndex
#print axioms NLA.Computation.TensorTrainApproximation.ColIndex
#assert_kind NLA.Computation.TensorTrainApproximation.join "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.join
#print axioms NLA.Computation.TensorTrainApproximation.join
#assert_kind NLA.Computation.TensorTrainApproximation.Unfold "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Unfold
#print axioms NLA.Computation.TensorTrainApproximation.Unfold
#assert_kind NLA.Computation.TensorTrainApproximation.Feasible "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Feasible
#print axioms NLA.Computation.TensorTrainApproximation.Feasible
#assert_kind NLA.Computation.TensorTrainApproximation.FrobeniusSq "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.FrobeniusSq
#print axioms NLA.Computation.TensorTrainApproximation.FrobeniusSq
#assert_kind NLA.Computation.TensorTrainApproximation.Optimum "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Optimum
#print axioms NLA.Computation.TensorTrainApproximation.Optimum
#assert_kind NLA.Computation.TensorTrainApproximation.DenseSize "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.DenseSize
#print axioms NLA.Computation.TensorTrainApproximation.DenseSize
#assert_kind NLA.Computation.TensorTrainApproximation.SuffixSize "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.SuffixSize
#print axioms NLA.Computation.TensorTrainApproximation.SuffixSize
#assert_kind NLA.Computation.TensorTrainApproximation.Offset "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Offset
#print axioms NLA.Computation.TensorTrainApproximation.Offset
#assert_kind NLA.Computation.TensorTrainApproximation.Decode "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Decode
#print axioms NLA.Computation.TensorTrainApproximation.Decode
#assert_kind NLA.Computation.TensorTrainApproximation.InputMemory "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.InputMemory
#print axioms NLA.Computation.TensorTrainApproximation.InputMemory
#assert_kind NLA.Computation.TensorTrainApproximation.Start "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Start
#print axioms NLA.Computation.TensorTrainApproximation.Start
#assert_kind NLA.Computation.TensorTrainApproximation.Returns "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Returns
#print axioms NLA.Computation.TensorTrainApproximation.Returns
#assert_kind NLA.Computation.TensorTrainApproximation.Size "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Size
#print axioms NLA.Computation.TensorTrainApproximation.Size
#assert_kind NLA.Statements.TR04.Target "definition"
#assert_trust kernel NLA.Statements.TR04.Target
#print axioms NLA.Statements.TR04.Target
#assert_kind NLA.Proofs.TR04.step_cost_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_cost_eq
#print axioms NLA.Proofs.TR04.step_cost_eq
#assert_kind NLA.Proofs.TR04.step_of_halted "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_of_halted
#print axioms NLA.Proofs.TR04.step_of_halted
#assert_kind NLA.Proofs.TR04.step_of_failed "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_of_failed
#print axioms NLA.Proofs.TR04.step_of_failed
#assert_kind NLA.Proofs.TR04.exists_legalTrace_of_step_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace_of_step_total
#print axioms NLA.Proofs.TR04.exists_legalTrace_of_step_total
#assert_kind NLA.Proofs.TR04.step_total_of_svd_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_total_of_svd_total
#print axioms NLA.Proofs.TR04.step_total_of_svd_total
#assert_kind NLA.Proofs.TR04.exists_legalTrace_of_svd_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace_of_svd_total
#print axioms NLA.Proofs.TR04.exists_legalTrace_of_svd_total
#assert_kind NLA.Proofs.TR04.SVD.Space "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.Space
#print axioms NLA.Proofs.TR04.SVD.Space
#assert_kind NLA.Proofs.TR04.SVD.rightBasis "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.rightBasis
#print axioms NLA.Proofs.TR04.SVD.rightBasis
#assert_kind NLA.Proofs.TR04.SVD.norm_image_rightBasis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_image_rightBasis
#print axioms NLA.Proofs.TR04.SVD.norm_image_rightBasis
#assert_kind NLA.Proofs.TR04.SVD.inner_image_rightBasis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.inner_image_rightBasis
#print axioms NLA.Proofs.TR04.SVD.inner_image_rightBasis
#assert_kind NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#print axioms NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#assert_kind NLA.Proofs.TR04.SVD.range_finrank_le_domain "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_domain
#print axioms NLA.Proofs.TR04.SVD.range_finrank_le_domain
#assert_kind NLA.Proofs.TR04.SVD.range_finrank_le_codomain "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#print axioms NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#assert_kind NLA.Proofs.TR04.SVD.leftVector "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.leftVector
#print axioms NLA.Proofs.TR04.SVD.leftVector
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#print axioms NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#assert_kind NLA.Proofs.TR04.SVD.exists_leftBasis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_leftBasis
#print axioms NLA.Proofs.TR04.SVD.exists_leftBasis
#assert_kind NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#print axioms NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#assert_kind NLA.Proofs.TR04.SVD.sum_fin_truncate "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_truncate
#print axioms NLA.Proofs.TR04.SVD.sum_fin_truncate
#assert_kind NLA.Proofs.TR04.SVD.exists_validSVD "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_validSVD
#print axioms NLA.Proofs.TR04.SVD.exists_validSVD
#assert_kind NLA.Proofs.TR04.step_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_total
#print axioms NLA.Proofs.TR04.step_total
#assert_kind NLA.Proofs.TR04.exists_legalTrace "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace
#print axioms NLA.Proofs.TR04.exists_legalTrace
#assert_kind NLA.Proofs.TR04.legalTrace_cost_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.legalTrace_cost_eq
#print axioms NLA.Proofs.TR04.legalTrace_cost_eq
#assert_kind NLA.Proofs.TR04.costThrough_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_zero
#print axioms NLA.Proofs.TR04.costThrough_zero
#assert_kind NLA.Proofs.TR04.costThrough_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_succ
#print axioms NLA.Proofs.TR04.costThrough_succ
#assert_kind NLA.Proofs.TR04.charge_pos_of_running "theorem"
#assert_trust kernel NLA.Proofs.TR04.charge_pos_of_running
#print axioms NLA.Proofs.TR04.charge_pos_of_running
#assert_kind NLA.Proofs.TR04.legalTrace_halted_state_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.legalTrace_halted_state_add
#print axioms NLA.Proofs.TR04.legalTrace_halted_state_add
#assert_kind NLA.Proofs.TR04.costThrough_add_of_halted "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_add_of_halted
#print axioms NLA.Proofs.TR04.costThrough_add_of_halted
#assert_kind NLA.Proofs.TR04.machineState_ext "theorem"
#assert_trust kernel NLA.Proofs.TR04.machineState_ext
#print axioms NLA.Proofs.TR04.machineState_ext
#assert_kind NLA.Proofs.TR04.instructionIsSVD "definition"
#assert_trust kernel NLA.Proofs.TR04.instructionIsSVD
#print axioms NLA.Proofs.TR04.instructionIsSVD
#assert_kind NLA.Proofs.TR04.step_iff_ordinary_of_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_iff_ordinary_of_scalar
#print axioms NLA.Proofs.TR04.step_iff_ordinary_of_scalar
#assert_kind NLA.Proofs.TR04.legalTrace_scalar_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.legalTrace_scalar_prefix
#print axioms NLA.Proofs.TR04.legalTrace_scalar_prefix
#assert_kind NLA.Proofs.TR04.costThrough_scalar_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_scalar_prefix
#print axioms NLA.Proofs.TR04.costThrough_scalar_prefix
#assert_kind NLA.Proofs.TR04.charge_le_one_of_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.charge_le_one_of_scalar
#print axioms NLA.Proofs.TR04.charge_le_one_of_scalar
#assert_kind NLA.Proofs.TR04.costThrough_le_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_le_scalar
#print axioms NLA.Proofs.TR04.costThrough_le_scalar
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram
#assert_kind NLA.Proofs.TR04.MatrixMultiplyScratch "inductive"
#assert_trust kernel NLA.Proofs.TR04.MatrixMultiplyScratch
#print axioms NLA.Proofs.TR04.MatrixMultiplyScratch
#assert_kind NLA.Proofs.TR04.matrixMultiplyState "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyState
#print axioms NLA.Proofs.TR04.matrixMultiplyState
#assert_kind NLA.Proofs.TR04.matrixMultiplyCellState "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyCellState
#print axioms NLA.Proofs.TR04.matrixMultiplyCellState
#assert_kind NLA.Proofs.TR04.matrixMultiplyInnerState "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyInnerState
#print axioms NLA.Proofs.TR04.matrixMultiplyInnerState
#assert_kind NLA.Proofs.TR04.matrixMultiplyRowState "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyRowState
#print axioms NLA.Proofs.TR04.matrixMultiplyRowState
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_scalar
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_scalar
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_cell_setup "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cell_setup
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cell_setup
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_inner_eight "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_inner_eight
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_inner_eight
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_inner_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_inner_iterations
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_inner_iterations
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_cell_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cell_exit
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cell_exit
#assert_kind NLA.Proofs.TR04.matrixMultiplyCellTime "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyCellTime
#print axioms NLA.Proofs.TR04.matrixMultiplyCellTime
#assert_kind NLA.Proofs.TR04.matrixMultiplyRowTime "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyRowTime
#print axioms NLA.Proofs.TR04.matrixMultiplyRowTime
#assert_kind NLA.Proofs.TR04.matrixMultiplyTime "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyTime
#print axioms NLA.Proofs.TR04.matrixMultiplyTime
#assert_kind NLA.Proofs.TR04.matrixMultiplyStart "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyStart
#print axioms NLA.Proofs.TR04.matrixMultiplyStart
#assert_kind NLA.Proofs.TR04.matrixMultiplyStart_eq_row "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyStart_eq_row
#print axioms NLA.Proofs.TR04.matrixMultiplyStart_eq_row
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_cell "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cell
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cell
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_cells "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_cells
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_cells
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_row_setup "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_row_setup
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_row_setup
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_row_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_row_exit
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_row_exit
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_row "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_row
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_row
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_rows "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_rows
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_rows
#assert_kind NLA.Proofs.TR04.matrixMultiplyFinalState "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyFinalState
#print axioms NLA.Proofs.TR04.matrixMultiplyFinalState
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_exit
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_exit
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_trace_result
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_trace_result
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_trace_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_trace_product
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_trace_product
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost
#assert_kind NLA.Proofs.TR04.matrixMultiplyTime_le_cubic "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyTime_le_cubic
#print axioms NLA.Proofs.TR04.matrixMultiplyTime_le_cubic
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_run "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_run
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_run

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData)
    (hr : p.bRowStride = p.inner) (hc : p.bColStride = 1) :
    p.leftMatrix = readMatrix p.memory p.rows p.inner p.bBase := @NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense p hr hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData)
    (hr : p.cRowStride = 1) (hc : p.cColStride = p.inner) :
    p.rightMatrix = (readMatrix p.memory p.cols p.inner p.cBase).transpose := @NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose p hr hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData)
    (i : Fin p.rows) (j : Fin p.cols) :
    p.productMatrix i j = p.partialProduct i.val j.val p.inner := @NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry p i j
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData)
    (hbr : p.bRowStride = p.inner) (hbc : p.bColStride = 1)
    (hcr : p.cRowStride = p.cols) (hcc : p.cColStride = 1)
    (hb : DisjointBlocks p.bBase (p.rows * p.inner) p.dBase (p.rows * p.cols))
    (hc : DisjointBlocks p.cBase (p.inner * p.cols) p.dBase (p.rows * p.cols)) :
    p.InputsOutsideOutput := @NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput p hbr hbc hcr hcc hb hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData) :
    ∃ trace : Trace matrixMultiplyProgram,
      LegalTrace matrixMultiplyProgram (matrixMultiplyStart p) trace := @NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace p
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyRowState p 0 scratch) trace) :
    (trace.state (matrixMultiplyTime p)).status = .halted p.dBase ∧
    readMatrix (trace.state (matrixMultiplyTime p)).memory p.rows p.cols p.dBase =
      p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (trace.state (matrixMultiplyTime p)).memory address = p.memory address) := @NLA.Proofs.TR04.matrixMultiplyProgram_trace_product p h scratch trace htrace
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData)
    (scratch : MatrixMultiplyScratch) (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyRowState p 0 scratch) trace) :
    CostThrough matrixMultiplyProgram trace (matrixMultiplyTime p) ≤
      ((8 * p.inner + 11) * p.cols + 4) * p.rows + 2 := @NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost p scratch trace htrace
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData) :
    matrixMultiplyTime p ≤ 17 * (p.rows + p.inner + p.cols + 1) ^ 3 := @NLA.Proofs.TR04.matrixMultiplyTime_le_cubic p
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example (p : MatrixMultiplyData) (h : p.InputsOutsideOutput)
    (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyStart p) trace) :
    (trace.state (matrixMultiplyTime p)).status = .halted p.dBase ∧
    readMatrix (trace.state (matrixMultiplyTime p)).memory p.rows p.cols p.dBase =
      p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (trace.state (matrixMultiplyTime p)).memory address = p.memory address) ∧
    CostThrough matrixMultiplyProgram trace (matrixMultiplyTime p) ≤
      17 * (p.rows + p.inner + p.cols + 1) ^ 3 := @NLA.Proofs.TR04.matrixMultiplyProgram_run p h trace htrace
end NLA.Proofs.TR04
end
