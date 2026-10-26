import NLA.Proofs.TR04.MachineTensorMultiplyTrace

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
#assert_kind NLA.Proofs.TR04.copyProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.copyProgram
#print axioms NLA.Proofs.TR04.copyProgram
#assert_kind NLA.Proofs.TR04.copiedMemory "definition"
#assert_trust kernel NLA.Proofs.TR04.copiedMemory
#print axioms NLA.Proofs.TR04.copiedMemory
#assert_kind NLA.Proofs.TR04.copyLoopState "definition"
#assert_trust kernel NLA.Proofs.TR04.copyLoopState
#print axioms NLA.Proofs.TR04.copyLoopState
#assert_kind NLA.Proofs.TR04.copiedMemory_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.copiedMemory_zero
#print axioms NLA.Proofs.TR04.copiedMemory_zero
#assert_kind NLA.Proofs.TR04.copiedMemory_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.copiedMemory_outside
#print axioms NLA.Proofs.TR04.copiedMemory_outside
#assert_kind NLA.Proofs.TR04.copiedMemory_source_next "theorem"
#assert_trust kernel NLA.Proofs.TR04.copiedMemory_source_next
#print axioms NLA.Proofs.TR04.copiedMemory_source_next
#assert_kind NLA.Proofs.TR04.copiedMemory_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.copiedMemory_succ
#print axioms NLA.Proofs.TR04.copiedMemory_succ
#assert_kind NLA.Proofs.TR04.copyProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_scalar
#print axioms NLA.Proofs.TR04.copyProgram_scalar
#assert_kind NLA.Proofs.TR04.copyProgram_six_steps "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_six_steps
#print axioms NLA.Proofs.TR04.copyProgram_six_steps
#assert_kind NLA.Proofs.TR04.copyProgram_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_iterations
#print axioms NLA.Proofs.TR04.copyProgram_iterations
#assert_kind NLA.Proofs.TR04.copyFinalState "definition"
#assert_trust kernel NLA.Proofs.TR04.copyFinalState
#print axioms NLA.Proofs.TR04.copyFinalState
#assert_kind NLA.Proofs.TR04.copyProgram_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_exit
#print axioms NLA.Proofs.TR04.copyProgram_exit
#assert_kind NLA.Proofs.TR04.copyProgram_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_trace_result
#print axioms NLA.Proofs.TR04.copyProgram_trace_result
#assert_kind NLA.Proofs.TR04.copyProgram_trace_cells "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_trace_cells
#print axioms NLA.Proofs.TR04.copyProgram_trace_cells
#assert_kind NLA.Proofs.TR04.copyProgram_trace_cost "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_trace_cost
#print axioms NLA.Proofs.TR04.copyProgram_trace_cost
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram
#print axioms NLA.Proofs.TR04.decodeNaturalProgram
#assert_kind NLA.Proofs.TR04.decodeNaturalLoopState "definition"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalLoopState
#print axioms NLA.Proofs.TR04.decodeNaturalLoopState
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_scalar
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_scalar
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_three_steps "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_three_steps
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_three_steps
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_iterations
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_iterations
#assert_kind NLA.Proofs.TR04.decodeNaturalFinalState "definition"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalFinalState
#print axioms NLA.Proofs.TR04.decodeNaturalFinalState
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_exit
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_exit
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_trace_result
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_trace_result
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_trace_cost "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_trace_cost
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_trace_cost
#assert_kind NLA.Proofs.TR04.instructionIsHalt "definition"
#assert_trust kernel NLA.Proofs.TR04.instructionIsHalt
#print axioms NLA.Proofs.TR04.instructionIsHalt
#assert_kind NLA.Proofs.TR04.relocateInstruction "definition"
#assert_trust kernel NLA.Proofs.TR04.relocateInstruction
#print axioms NLA.Proofs.TR04.relocateInstruction
#assert_kind NLA.Proofs.TR04.RoutineEmbedding "inductive"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding
#print axioms NLA.Proofs.TR04.RoutineEmbedding
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.Relates "inductive"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.Relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.Relates
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.Relates.real_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.Relates.real_apply
#print axioms NLA.Proofs.TR04.RoutineEmbedding.Relates.real_apply
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.Relates.natural_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.Relates.natural_apply
#print axioms NLA.Proofs.TR04.RoutineEmbedding.Relates.natural_apply
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_relates
#assert_kind NLA.Proofs.TR04.instructionIsSVD_relocate "theorem"
#assert_trust kernel NLA.Proofs.TR04.instructionIsSVD_relocate
#print axioms NLA.Proofs.TR04.instructionIsSVD_relocate
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.charge_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.charge_eq
#print axioms NLA.Proofs.TR04.RoutineEmbedding.charge_eq
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.scalar_step "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_step
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_step
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_prefix
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_prefix
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost_le
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost_le
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_real_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_real_outside
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_natural_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_natural_outside
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_real_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_real_outside
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_natural_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_natural_outside
#assert_kind NLA.Proofs.TR04.copyProgram_nohalt_phase "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_nohalt_phase
#print axioms NLA.Proofs.TR04.copyProgram_nohalt_phase
#assert_kind NLA.Proofs.TR04.copyProgram_nohalt_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_nohalt_prefix
#print axioms NLA.Proofs.TR04.copyProgram_nohalt_prefix
#assert_kind NLA.Proofs.TR04.copyReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.copyReturnState
#print axioms NLA.Proofs.TR04.copyReturnState
#assert_kind NLA.Proofs.TR04.copyProgram_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.copyProgram_return
#print axioms NLA.Proofs.TR04.copyProgram_return
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.copy_run "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.copy_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.copy_run
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_nohalt_phase "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_nohalt_phase
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_nohalt_phase
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_nohalt_initial "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_nohalt_initial
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_nohalt_initial
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_nohalt_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_nohalt_prefix
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_nohalt_prefix
#assert_kind NLA.Proofs.TR04.decodeNaturalReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalReturnState
#print axioms NLA.Proofs.TR04.decodeNaturalReturnState
#assert_kind NLA.Proofs.TR04.decodeNaturalProgram_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_return
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_return
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run
#assert_kind NLA.Proofs.TR04.shiftedTrace "definition"
#assert_trust kernel NLA.Proofs.TR04.shiftedTrace
#print axioms NLA.Proofs.TR04.shiftedTrace
#assert_kind NLA.Proofs.TR04.legalTrace_shift "theorem"
#assert_trust kernel NLA.Proofs.TR04.legalTrace_shift
#print axioms NLA.Proofs.TR04.legalTrace_shift
#assert_kind NLA.Proofs.TR04.costThrough_shift "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_shift
#print axioms NLA.Proofs.TR04.costThrough_shift
#assert_kind NLA.Proofs.TR04.costThrough_compose_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_compose_le
#print axioms NLA.Proofs.TR04.costThrough_compose_le
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.copy_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.copy_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.copy_run_at
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run_at
#assert_kind NLA.Proofs.TR04.ordinaryStep_eq_of_stopped "theorem"
#assert_trust kernel NLA.Proofs.TR04.ordinaryStep_eq_of_stopped
#print axioms NLA.Proofs.TR04.ordinaryStep_eq_of_stopped
#assert_kind NLA.Proofs.TR04.ordinary_iterate_eq_of_stopped "theorem"
#assert_trust kernel NLA.Proofs.TR04.ordinary_iterate_eq_of_stopped
#print axioms NLA.Proofs.TR04.ordinary_iterate_eq_of_stopped
#assert_kind NLA.Proofs.TR04.ordinary_running_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.ordinary_running_prefix
#print axioms NLA.Proofs.TR04.ordinary_running_prefix
#assert_kind NLA.Proofs.TR04.ordinary_nohalt_prefix_of_running "theorem"
#assert_trust kernel NLA.Proofs.TR04.ordinary_nohalt_prefix_of_running
#print axioms NLA.Proofs.TR04.ordinary_nohalt_prefix_of_running
#assert_kind NLA.Proofs.TR04.matrixMultiplyReturnTime "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnTime
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnTime
#assert_kind NLA.Proofs.TR04.matrixMultiplyReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnState
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnState
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_return_step "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_return_step
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_return_step
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_return
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_return
#assert_kind NLA.Proofs.TR04.matrixMultiplyReturnState_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnState_product
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnState_product
#assert_kind NLA.Proofs.TR04.matrixMultiplyReturnTime_le_cubic "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyReturnTime_le_cubic
#print axioms NLA.Proofs.TR04.matrixMultiplyReturnTime_le_cubic
#assert_kind NLA.Proofs.TR04.matrixMultiplyProgram_nohalt "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixMultiplyProgram_nohalt
#print axioms NLA.Proofs.TR04.matrixMultiplyProgram_nohalt
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_run_at
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_product_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_product_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_product_at
#assert_kind NLA.Proofs.TR04.splitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.splitIndex
#print axioms NLA.Proofs.TR04.splitIndex
#assert_kind NLA.Proofs.TR04.splitIndex_join "theorem"
#assert_trust kernel NLA.Proofs.TR04.splitIndex_join
#print axioms NLA.Proofs.TR04.splitIndex_join
#assert_kind NLA.Proofs.TR04.join_splitIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.join_splitIndex
#print axioms NLA.Proofs.TR04.join_splitIndex
#assert_kind NLA.Proofs.TR04.joinEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.joinEquiv
#print axioms NLA.Proofs.TR04.joinEquiv
#assert_kind NLA.Proofs.TR04.unfoldLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.unfoldLinearEquiv
#print axioms NLA.Proofs.TR04.unfoldLinearEquiv
#assert_kind NLA.Proofs.TR04.unfoldContinuousLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.unfoldContinuousLinearEquiv
#print axioms NLA.Proofs.TR04.unfoldContinuousLinearEquiv
#assert_kind NLA.Proofs.TR04.unfoldLinearEquiv_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfoldLinearEquiv_apply
#print axioms NLA.Proofs.TR04.unfoldLinearEquiv_apply
#assert_kind NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply
#print axioms NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply
#assert_kind NLA.Proofs.TR04.continuous_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.continuous_unfold
#print axioms NLA.Proofs.TR04.continuous_unfold
#assert_kind NLA.Proofs.TR04.unfold_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_zero
#print axioms NLA.Proofs.TR04.unfold_zero
#assert_kind NLA.Proofs.TR04.unfold_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_add
#print axioms NLA.Proofs.TR04.unfold_add
#assert_kind NLA.Proofs.TR04.unfold_smul "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_smul
#print axioms NLA.Proofs.TR04.unfold_smul
#assert_kind NLA.Proofs.TR04.unfold_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_injective
#print axioms NLA.Proofs.TR04.unfold_injective
#assert_kind NLA.Proofs.TR04.sum_unfold_indices "theorem"
#assert_trust kernel NLA.Proofs.TR04.sum_unfold_indices
#print axioms NLA.Proofs.TR04.sum_unfold_indices
#assert_kind NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum
#print axioms NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum
#assert_kind NLA.Proofs.TR04.TensorFormat.Index "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Index
#print axioms NLA.Proofs.TR04.TensorFormat.Index
#assert_kind NLA.Proofs.TR04.TensorFormat.indexFintype "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.indexFintype
#print axioms NLA.Proofs.TR04.TensorFormat.indexFintype
#assert_kind NLA.Proofs.TR04.TensorFormat.Tensor "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Tensor
#print axioms NLA.Proofs.TR04.TensorFormat.Tensor
#assert_kind NLA.Proofs.TR04.TensorFormat.splitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.splitIndex
#print axioms NLA.Proofs.TR04.TensorFormat.splitIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.joinIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.joinIndex
#print axioms NLA.Proofs.TR04.TensorFormat.joinIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.joinIndex_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.joinIndex_zero
#print axioms NLA.Proofs.TR04.TensorFormat.joinIndex_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.join_splitIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.join_splitIndex
#print axioms NLA.Proofs.TR04.TensorFormat.join_splitIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.split_joinIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.split_joinIndex
#print axioms NLA.Proofs.TR04.TensorFormat.split_joinIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.splitEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.splitEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.splitEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold
#print axioms NLA.Proofs.TR04.TensorFormat.unfold
#assert_kind NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.energy "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy
#print axioms NLA.Proofs.TR04.TensorFormat.energy
#assert_kind NLA.Proofs.TR04.TensorFormat.error "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error
#print axioms NLA.Proofs.TR04.TensorFormat.error
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_nonneg
#print axioms NLA.Proofs.TR04.TensorFormat.energy_nonneg
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_unfold
#print axioms NLA.Proofs.TR04.TensorFormat.energy_unfold
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_zero
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_sub
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_sub
#assert_kind NLA.Proofs.TR04.TensorFormat.error_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_unfold
#print axioms NLA.Proofs.TR04.TensorFormat.error_unfold
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_zero
#print axioms NLA.Proofs.TR04.TensorFormat.energy_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.error_zero_right "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_zero_right
#print axioms NLA.Proofs.TR04.TensorFormat.error_zero_right
#assert_kind NLA.Proofs.TR04.TensorFormat.error_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_nonneg
#print axioms NLA.Proofs.TR04.TensorFormat.error_nonneg
#assert_kind NLA.Proofs.TR04.TensorFormat.card_index "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.card_index
#print axioms NLA.Proofs.TR04.TensorFormat.card_index
#assert_kind NLA.Proofs.TR04.TensorFormat.modeList "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.modeList
#print axioms NLA.Proofs.TR04.TensorFormat.modeList
#assert_kind NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn
#print axioms NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn
#assert_kind NLA.Proofs.TR04.TensorFormat.length_modeList "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.length_modeList
#print axioms NLA.Proofs.TR04.TensorFormat.length_modeList
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.original_error_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_error_eq
#print axioms NLA.Proofs.TR04.TensorFormat.original_error_eq
#assert_kind NLA.Proofs.TR04.SVD.OrthonormalColumns "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.OrthonormalColumns
#print axioms NLA.Proofs.TR04.SVD.OrthonormalColumns
#assert_kind NLA.Proofs.TR04.SVD.transpose_mul_eq_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.transpose_mul_eq_one
#print axioms NLA.Proofs.TR04.SVD.transpose_mul_eq_one
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_submatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_submatrix
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_submatrix
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_inner "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_inner
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_inner
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_sum_sq "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_sum_sq
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_sum_sq
#assert_kind NLA.Proofs.TR04.SVD.matrixEnergy "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy
#print axioms NLA.Proofs.TR04.SVD.matrixEnergy
#assert_kind NLA.Proofs.TR04.SVD.synthesis "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.synthesis
#print axioms NLA.Proofs.TR04.SVD.synthesis
#assert_kind NLA.Proofs.TR04.SVD.validSVD_eq_synthesis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eq_synthesis
#print axioms NLA.Proofs.TR04.SVD.validSVD_eq_synthesis
#assert_kind NLA.Proofs.TR04.SVD.synthesis_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.synthesis_energy
#print axioms NLA.Proofs.TR04.SVD.synthesis_energy
#assert_kind NLA.Proofs.TR04.SVD.validSVD_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_energy
#print axioms NLA.Proofs.TR04.SVD.validSVD_energy
#assert_kind NLA.Proofs.TR04.SVD.synthesis_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.synthesis_sub
#print axioms NLA.Proofs.TR04.SVD.synthesis_sub
#assert_kind NLA.Proofs.TR04.SVD.validSVD_error_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_error_energy
#print axioms NLA.Proofs.TR04.SVD.validSVD_error_energy
#assert_kind NLA.Proofs.TR04.SVD.truncate "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.truncate
#print axioms NLA.Proofs.TR04.SVD.truncate
#assert_kind NLA.Proofs.TR04.SVD.tailEnergy "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy
#print axioms NLA.Proofs.TR04.SVD.tailEnergy
#assert_kind NLA.Proofs.TR04.SVD.validSVD_truncate_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_truncate_error
#print axioms NLA.Proofs.TR04.SVD.validSVD_truncate_error
#assert_kind NLA.Proofs.TR04.TensorFormat.firstMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.firstMatrix
#print axioms NLA.Proofs.TR04.TensorFormat.firstMatrix
#assert_kind NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.contract "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contract
#print axioms NLA.Proofs.TR04.TensorFormat.contract
#assert_kind NLA.Proofs.TR04.TensorFormat.lift "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.lift
#print axioms NLA.Proofs.TR04.TensorFormat.lift
#assert_kind NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_zero
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_sub
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_sub
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_comp "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_comp
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_comp
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_one
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_one
#assert_kind NLA.Proofs.TR04.TensorFormat.contract_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contract_lift
#print axioms NLA.Proofs.TR04.TensorFormat.contract_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_firstMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_firstMatrix
#print axioms NLA.Proofs.TR04.TensorFormat.energy_firstMatrix
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_lift
#print axioms NLA.Proofs.TR04.TensorFormat.energy_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.error_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_lift
#print axioms NLA.Proofs.TR04.TensorFormat.error_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.inner "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.inner
#print axioms NLA.Proofs.TR04.TensorFormat.inner
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_add
#print axioms NLA.Proofs.TR04.TensorFormat.energy_add
#assert_kind NLA.Proofs.TR04.TensorFormat.inner_contract_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.inner_contract_lift
#print axioms NLA.Proofs.TR04.TensorFormat.inner_contract_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.residual_inner_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.residual_inner_lift
#print axioms NLA.Proofs.TR04.TensorFormat.residual_inner_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.error_lift_decomposition "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_lift_decomposition
#print axioms NLA.Proofs.TR04.TensorFormat.error_lift_decomposition
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_contract_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_contract_le
#print axioms NLA.Proofs.TR04.TensorFormat.energy_contract_le
#assert_kind NLA.Proofs.TR04.TensorFormat.error_contract_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_contract_le
#print axioms NLA.Proofs.TR04.TensorFormat.error_contract_le
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixAction "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixAction
#print axioms NLA.Proofs.TR04.TensorFormat.prefixAction
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le
#assert_kind NLA.Proofs.TR04.TensorFormat.headIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.headIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.headIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_one
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_one
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le
#assert_kind NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_reindex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_reindex
#print axioms NLA.Proofs.TR04.TensorFormat.energy_reindex
#assert_kind NLA.Proofs.TR04.TensorFormat.error_reindex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_reindex
#print axioms NLA.Proofs.TR04.TensorFormat.error_reindex
#assert_kind NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.merge "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.merge
#print axioms NLA.Proofs.TR04.TensorFormat.merge
#assert_kind NLA.Proofs.TR04.TensorFormat.merge_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.merge_apply
#print axioms NLA.Proofs.TR04.TensorFormat.merge_apply
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_merge
#print axioms NLA.Proofs.TR04.TensorFormat.energy_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.error_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_merge
#print axioms NLA.Proofs.TR04.TensorFormat.error_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_merge
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_merge
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.projected_error_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.projected_error_eq
#print axioms NLA.Proofs.TR04.TensorFormat.projected_error_eq
#assert_kind NLA.Proofs.TR04.SVD.truncate_rank_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.truncate_rank_le
#print axioms NLA.Proofs.TR04.SVD.truncate_rank_le
#assert_kind NLA.Proofs.TR04.SVD.matrixEnergy_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_nonneg
#print axioms NLA.Proofs.TR04.SVD.matrixEnergy_nonneg
#assert_kind NLA.Proofs.TR04.SVD.matrixEnergy_entry_sq_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_entry_sq_le
#print axioms NLA.Proofs.TR04.SVD.matrixEnergy_entry_sq_le
#assert_kind NLA.Proofs.TR04.SVD.matrixEnergy_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_eq_zero_iff
#print axioms NLA.Proofs.TR04.SVD.matrixEnergy_eq_zero_iff
#assert_kind NLA.Proofs.TR04.SVD.matrixError_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixError_eq_zero_iff
#print axioms NLA.Proofs.TR04.SVD.matrixError_eq_zero_iff
#assert_kind NLA.Proofs.TR04.SVD.validSVD_zero_tail_iff_truncate "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_zero_tail_iff_truncate
#print axioms NLA.Proofs.TR04.SVD.validSVD_zero_tail_iff_truncate
#assert_kind NLA.Proofs.TR04.SVD.tailEnergy_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy_nonneg
#print axioms NLA.Proofs.TR04.SVD.tailEnergy_nonneg
#assert_kind NLA.Proofs.TR04.SVD.prefixEnergy "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy
#print axioms NLA.Proofs.TR04.SVD.prefixEnergy
#assert_kind NLA.Proofs.TR04.SVD.weightDefect "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.weightDefect
#print axioms NLA.Proofs.TR04.SVD.weightDefect
#assert_kind NLA.Proofs.TR04.SVD.prefix_count "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_count
#print axioms NLA.Proofs.TR04.SVD.prefix_count
#assert_kind NLA.Proofs.TR04.SVD.weighted_prefix_defect "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_prefix_defect
#print axioms NLA.Proofs.TR04.SVD.weighted_prefix_defect
#assert_kind NLA.Proofs.TR04.SVD.weightDefect_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weightDefect_nonneg
#print axioms NLA.Proofs.TR04.SVD.weightDefect_nonneg
#assert_kind NLA.Proofs.TR04.SVD.weighted_prefix_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_prefix_le
#print axioms NLA.Proofs.TR04.SVD.weighted_prefix_le
#assert_kind NLA.Proofs.TR04.SVD.weighted_prefix_eq_support "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_prefix_eq_support
#print axioms NLA.Proofs.TR04.SVD.weighted_prefix_eq_support
#assert_kind NLA.Proofs.TR04.SVD.matrixColumn "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn
#print axioms NLA.Proofs.TR04.SVD.matrixColumn
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix
#print axioms NLA.Proofs.TR04.SVD.projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.matrixColumn_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.matrixColumn_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.matrixColumn_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_sub
#print axioms NLA.Proofs.TR04.SVD.matrixColumn_sub
#assert_kind NLA.Proofs.TR04.SVD.matrixEnergy_eq_sum_column_norm "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_eq_sum_column_norm
#print axioms NLA.Proofs.TR04.SVD.matrixEnergy_eq_sum_column_norm
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix_energy_decomposition "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_energy_decomposition
#print axioms NLA.Proofs.TR04.SVD.projectMatrix_energy_decomposition
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix_error_decomposition "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_error_decomposition
#print axioms NLA.Proofs.TR04.SVD.projectMatrix_error_decomposition
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix_error_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_error_le
#print axioms NLA.Proofs.TR04.SVD.projectMatrix_error_le
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix_error_eq_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_error_eq_iff
#print axioms NLA.Proofs.TR04.SVD.projectMatrix_error_eq_iff
#assert_kind NLA.Proofs.TR04.SVD.exists_basis_of_orthonormalColumns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_basis_of_orthonormalColumns
#print axioms NLA.Proofs.TR04.SVD.exists_basis_of_orthonormalColumns
#assert_kind NLA.Proofs.TR04.SVD.projection_norm_sq_basis_sum "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projection_norm_sq_basis_sum
#print axioms NLA.Proofs.TR04.SVD.projection_norm_sq_basis_sum
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight
#print axioms NLA.Proofs.TR04.SVD.projectionWeight
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_nonneg
#print axioms NLA.Proofs.TR04.SVD.projectionWeight_nonneg
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight_le_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_le_one
#print axioms NLA.Proofs.TR04.SVD.projectionWeight_le_one
#assert_kind NLA.Proofs.TR04.SVD.sum_projectionWeight "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_projectionWeight
#print axioms NLA.Proofs.TR04.SVD.sum_projectionWeight
#assert_kind NLA.Proofs.TR04.SVD.right_synthesis_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.right_synthesis_energy
#print axioms NLA.Proofs.TR04.SVD.right_synthesis_energy
#assert_kind NLA.Proofs.TR04.SVD.matrixColumn_synthesis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_synthesis
#print axioms NLA.Proofs.TR04.SVD.matrixColumn_synthesis
#assert_kind NLA.Proofs.TR04.SVD.validSVD_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_project_energy
#print axioms NLA.Proofs.TR04.SVD.validSVD_project_energy
#assert_kind NLA.Proofs.TR04.SVD.sum_fin_prefix_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_prefix_le
#print axioms NLA.Proofs.TR04.SVD.sum_fin_prefix_le
#assert_kind NLA.Proofs.TR04.SVD.sum_svd_projectionWeight_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_svd_projectionWeight_le
#print axioms NLA.Proofs.TR04.SVD.sum_svd_projectionWeight_le
#assert_kind NLA.Proofs.TR04.SVD.singularSquares_antitone "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSquares_antitone
#print axioms NLA.Proofs.TR04.SVD.singularSquares_antitone
#assert_kind NLA.Proofs.TR04.SVD.prefix_add_tail "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_add_tail
#print axioms NLA.Proofs.TR04.SVD.prefix_add_tail
#assert_kind NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_of_length_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_of_length_le
#print axioms NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_of_length_le
#assert_kind NLA.Proofs.TR04.SVD.columnSpace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.columnSpace
#print axioms NLA.Proofs.TR04.SVD.columnSpace
#assert_kind NLA.Proofs.TR04.SVD.matrixColumn_mem_columnSpace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_mem_columnSpace
#print axioms NLA.Proofs.TR04.SVD.matrixColumn_mem_columnSpace
#assert_kind NLA.Proofs.TR04.SVD.finrank_columnSpace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.finrank_columnSpace
#print axioms NLA.Proofs.TR04.SVD.finrank_columnSpace
#assert_kind NLA.Proofs.TR04.SVD.validSVD_eckartYoung "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung
#print axioms NLA.Proofs.TR04.SVD.validSVD_eckartYoung
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight_eq_one_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_eq_one_iff
#print axioms NLA.Proofs.TR04.SVD.projectionWeight_eq_one_iff
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_eq_zero_iff
#print axioms NLA.Proofs.TR04.SVD.projectionWeight_eq_zero_iff
#assert_kind NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq
#print axioms NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq
#assert_kind NLA.Proofs.TR04.SVD.thresholdDefect "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.thresholdDefect
#print axioms NLA.Proofs.TR04.SVD.thresholdDefect
#assert_kind NLA.Proofs.TR04.SVD.prefix_count_of_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_count_of_le
#print axioms NLA.Proofs.TR04.SVD.prefix_count_of_le
#assert_kind NLA.Proofs.TR04.SVD.weighted_threshold_defect "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_threshold_defect
#print axioms NLA.Proofs.TR04.SVD.weighted_threshold_defect
#assert_kind NLA.Proofs.TR04.SVD.thresholdDefect_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.thresholdDefect_nonneg
#print axioms NLA.Proofs.TR04.SVD.thresholdDefect_nonneg
#assert_kind NLA.Proofs.TR04.SVD.weighted_threshold_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_threshold_le
#print axioms NLA.Proofs.TR04.SVD.weighted_threshold_le
#assert_kind NLA.Proofs.TR04.SVD.weighted_threshold_eq_support "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_threshold_eq_support
#print axioms NLA.Proofs.TR04.SVD.weighted_threshold_eq_support
#assert_kind NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_threshold "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_threshold
#print axioms NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_threshold
#assert_kind NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_last_retained "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_last_retained
#print axioms NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_last_retained
#assert_kind NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_iff
#print axioms NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_iff
#assert_kind NLA.Proofs.TR04.SVD.validSVD_rank_le_iff_tail_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_rank_le_iff_tail_zero
#print axioms NLA.Proofs.TR04.SVD.validSVD_rank_le_iff_tail_zero
#assert_kind NLA.Proofs.TR04.SVD.validSVD_truncate_best "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_truncate_best
#print axioms NLA.Proofs.TR04.SVD.validSVD_truncate_best
#assert_kind NLA.Proofs.TR04.SVD.validSVD_positive_tail "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_positive_tail
#print axioms NLA.Proofs.TR04.SVD.validSVD_positive_tail
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixSize "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixSize
#print axioms NLA.Proofs.TR04.TensorFormat.suffixSize
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_denseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.rank_denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_denseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.energy_denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_sub
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_sub
#assert_kind NLA.Proofs.TR04.TensorFormat.cappedRank "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.cappedRank
#print axioms NLA.Proofs.TR04.TensorFormat.cappedRank
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixFrame
#print axioms NLA.Proofs.TR04.TensorFormat.prefixFrame
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal
#print axioms NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection
#assert_kind NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le
#print axioms NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le
#assert_kind NLA.Proofs.TR04.TensorFormat.RankFeasible "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.RankFeasible
#print axioms NLA.Proofs.TR04.TensorFormat.RankFeasible
#assert_kind NLA.Proofs.TR04.TensorFormat.stepRank "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepRank
#print axioms NLA.Proofs.TR04.TensorFormat.stepRank
#assert_kind NLA.Proofs.TR04.TensorFormat.stepFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepFrame
#print axioms NLA.Proofs.TR04.TensorFormat.stepFrame
#assert_kind NLA.Proofs.TR04.TensorFormat.stepInput "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepInput
#print axioms NLA.Proofs.TR04.TensorFormat.stepInput
#assert_kind NLA.Proofs.TR04.TensorFormat.stepOutput "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepOutput
#print axioms NLA.Proofs.TR04.TensorFormat.stepOutput
#assert_kind NLA.Proofs.TR04.TensorFormat.Completion "inductive"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Completion
#print axioms NLA.Proofs.TR04.TensorFormat.Completion
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_exists "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_exists
#print axioms NLA.Proofs.TR04.TensorFormat.completion_exists
#assert_kind NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract
#print axioms NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_feasible
#print axioms NLA.Proofs.TR04.TensorFormat.completion_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.take_ofFn_modes "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.take_ofFn_modes
#print axioms NLA.Proofs.TR04.TensorFormat.take_ofFn_modes
#assert_kind NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes
#print axioms NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate
#print axioms NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate
#assert_kind NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate
#print axioms NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate
#assert_kind NLA.Proofs.TR04.TensorFormat.originalCut_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalCut_le
#print axioms NLA.Proofs.TR04.TensorFormat.originalCut_le
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRowEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRowEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalRowEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalColEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalColEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalColEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.original_join "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_join
#print axioms NLA.Proofs.TR04.TensorFormat.original_join
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_original
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_original
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_original
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_original
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRanks "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRanks
#print axioms NLA.Proofs.TR04.TensorFormat.originalRanks
#assert_kind NLA.Proofs.TR04.TensorFormat.original_feasible_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_feasible_iff
#print axioms NLA.Proofs.TR04.TensorFormat.original_feasible_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.radixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset
#assert_kind NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_lt
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_lt
#assert_kind NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode
#assert_kind NLA.Proofs.TR04.TensorFormat.cardToProdEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.cardToProdEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.cardToProdEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val
#print axioms NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val
#assert_kind NLA.Proofs.TR04.TensorFormat.prod_modeList "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prod_modeList
#print axioms NLA.Proofs.TR04.TensorFormat.prod_modeList
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorOffset "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_vector "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_vector
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_vector
#assert_kind NLA.Proofs.TR04.TensorFormat.original_radixOffset "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_radixOffset
#print axioms NLA.Proofs.TR04.TensorFormat.original_radixOffset
#assert_kind NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize
#assert_kind NLA.Proofs.TR04.TensorFormat.validSVD_reindex_columns "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.validSVD_reindex_columns
#print axioms NLA.Proofs.TR04.TensorFormat.validSVD_reindex_columns
#assert_kind NLA.Proofs.TR04.TensorFormat.radixDenseFirst "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixDenseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.radixDenseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixPermutation "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixPermutation
#print axioms NLA.Proofs.TR04.TensorFormat.suffixPermutation
#assert_kind NLA.Proofs.TR04.TensorFormat.radixDenseFirst_eq_reindex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixDenseFirst_eq_reindex
#print axioms NLA.Proofs.TR04.TensorFormat.radixDenseFirst_eq_reindex
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_eq_reindex_radix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_eq_reindex_radix
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_eq_reindex_radix
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_radixDenseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_radixDenseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.rank_radixDenseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_radixDenseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_radixDenseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.energy_radixDenseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.radix_validSVD_to_denseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radix_validSVD_to_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.radix_validSVD_to_denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_step_radix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_step_radix
#print axioms NLA.Proofs.TR04.TensorFormat.completion_step_radix
#assert_kind NLA.Proofs.TR04.TensorFormat.mode_suffix_dvd_prod "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.mode_suffix_dvd_prod
#print axioms NLA.Proofs.TR04.TensorFormat.mode_suffix_dvd_prod
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_pos
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_pos
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorOffset_cons "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset_cons
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset_cons
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorOffset_digit "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset_digit
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset_digit
#assert_kind NLA.Proofs.TR04.TensorFormat.original_decode_offset "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_decode_offset
#print axioms NLA.Proofs.TR04.TensorFormat.original_decode_offset
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_decode "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_decode
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_decode
#assert_kind NLA.Proofs.TR04.TensorFormat.denseToProdEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseToProdEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.denseToProdEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv_offset "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv_offset
#print axioms NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv_offset
#assert_kind NLA.Proofs.TR04.TensorFormat.original_offset_decode "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_decode
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_decode
#assert_kind NLA.Proofs.TR04.TensorFormat.original_offset_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_injective
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_injective
#assert_kind NLA.Proofs.TR04.TensorFormat.original_inputMemory_tensor_cell "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_inputMemory_tensor_cell
#print axioms NLA.Proofs.TR04.TensorFormat.original_inputMemory_tensor_cell
#assert_kind NLA.Proofs.TR04.TensorFormat.StoresTensor "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresTensor
#print axioms NLA.Proofs.TR04.TensorFormat.StoresTensor
#assert_kind NLA.Proofs.TR04.TensorFormat.StoresFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresFrame
#print axioms NLA.Proofs.TR04.TensorFormat.StoresFrame
#assert_kind NLA.Proofs.TR04.TensorFormat.tensor_suffixSize_eq_prod "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.tensor_suffixSize_eq_prod
#print axioms NLA.Proofs.TR04.TensorFormat.tensor_suffixSize_eq_prod
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_radixSuffixEquiv "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_radixSuffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_radixSuffixEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat
#assert_kind NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.radixDenseFirst_actFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixDenseFirst_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.radixDenseFirst_actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices
#assert_kind NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.StoresTensor.memory_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresTensor.memory_eq
#print axioms NLA.Proofs.TR04.TensorFormat.StoresTensor.memory_eq
#assert_kind NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.storesFrame_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesFrame_prefix
#print axioms NLA.Proofs.TR04.TensorFormat.storesFrame_prefix
#assert_kind NLA.Proofs.TR04.TensorFormat.StoresFrame.memory_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresFrame.memory_eq
#print axioms NLA.Proofs.TR04.TensorFormat.StoresFrame.memory_eq
#assert_kind NLA.Proofs.TR04.TensorFormat.storesTensor_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_original
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_original
#assert_kind NLA.Proofs.TR04.TensorFormat.actMultiplyData "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData
#assert_kind NLA.Proofs.TR04.TensorFormat.contractMultiplyData "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contractMultiplyData
#print axioms NLA.Proofs.TR04.TensorFormat.contractMultiplyData
#assert_kind NLA.Proofs.TR04.TensorFormat.liftMultiplyData "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.liftMultiplyData
#print axioms NLA.Proofs.TR04.TensorFormat.liftMultiplyData
#assert_kind NLA.Proofs.TR04.TensorFormat.actMultiplyData_left "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData_left
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData_left
#assert_kind NLA.Proofs.TR04.TensorFormat.actMultiplyData_right "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData_right
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData_right
#assert_kind NLA.Proofs.TR04.TensorFormat.actMultiplyData_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData_product
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData_product
#assert_kind NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product
#print axioms NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product
#assert_kind NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product
#print axioms NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product
#assert_kind NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe
#print axioms NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe
#assert_kind NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe
#print axioms NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.contract_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.contract_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.contract_run_at
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.lift_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.lift_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.lift_run_at

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (base : ℕ) (ns : List ℕ) (A : Tensor ns) :
    StoresTensor memory base ns A ↔
      ∀ i : Fin ns.prod, memory (base + i.val) = A (radixIndexEquiv ns i) := @NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat memory base ns A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example {m : ℕ} {ns : List ℕ}
    (memory : ℕ → ℝ) (base : ℕ) (A : Tensor (m :: ns)) :
    StoresTensor memory base (m :: ns) A ↔
      readMatrix memory m (suffixSize ns) base = radixDenseFirst A := @NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff m ns memory base A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (k n : ℕ) (ns : List ℕ)
    (i : Fin k) (j : Fin n) (x : Index ns) :
    radixOffset ((k * n) :: ns) (finProdFinEquiv (i, j), x) =
      radixOffset (k :: n :: ns) (i, j, x) := @NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices k n ns i j x
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (base k n : ℕ) (ns : List ℕ)
    (A : Tensor (k :: n :: ns)) :
    StoresTensor memory base (k :: n :: ns) A ↔
      StoresTensor memory base ((k * n) :: ns) (merge k n ns A) := @NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff memory base k n ns A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (base k n : ℕ) (ns : List ℕ)
    (A : Tensor ((k * n) :: ns)) :
    StoresTensor memory base ((k * n) :: ns) A ↔
      StoresTensor memory base (k :: n :: ns) ((merge k n ns).symm A) := @NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff memory base k n ns A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example {m q : ℕ} (memory : ℕ → ℝ) (base : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) :
    StoresFrame memory base q Q ↔ readMatrix memory m q base = Q := @NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff m q memory base Q
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example {m q : ℕ} (memory : ℕ → ℝ) (base : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) (hq : q ≤ m)
    (hU : readMatrix memory m m base = U) :
    StoresFrame memory base m (U.submatrix id (Fin.castLE hq)) := @NLA.Proofs.TR04.TensorFormat.storesFrame_prefix m q memory base U hq hU
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (S : NLA.Computation.TensorTrainApproximation.Shape)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) (memory : ℕ → ℝ) (base : ℕ)
    (h : ∀ x, memory (base + NLA.Computation.TensorTrainApproximation.Offset S x) = A x) :
    StoresTensor memory base (modeList S.mode) (originalTensorLinearEquiv S A) := @NLA.Proofs.TR04.TensorFormat.storesTensor_original S A memory base h
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (m :: ns)) (hA : StoresTensor memory inputBase (m :: ns) A) :
    (contractMultiplyData memory m q ns frameBase stride inputBase outputBase).productMatrix =
      radixDenseFirst (contract Q A) := @NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product m q ns memory frameBase stride inputBase outputBase Q hQ A hA
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (q :: ns)) (hA : StoresTensor memory inputBase (q :: ns) A) :
    (liftMultiplyData memory m q ns frameBase stride inputBase outputBase).productMatrix =
      radixDenseFirst (lift Q A) := @NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product m q ns memory frameBase stride inputBase outputBase Q hQ A hA
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (m q : ℕ) (ns : List ℕ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (hQ : DisjointBlocks frameBase (m * stride) outputBase (q * suffixSize ns))
    (hA : DisjointBlocks inputBase (m * suffixSize ns) outputBase (q * suffixSize ns)) :
    (contractMultiplyData memory m q ns frameBase stride inputBase outputBase).InputsOutsideOutput := @NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe memory m q ns frameBase stride inputBase outputBase hq hQ hA
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (m q : ℕ) (ns : List ℕ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (hQ : DisjointBlocks frameBase (m * stride) outputBase (m * suffixSize ns))
    (hA : DisjointBlocks inputBase (q * suffixSize ns) outputBase (m * suffixSize ns)) :
    (liftMultiplyData memory m q ns frameBase stride inputBase outputBase).InputsOutsideOutput := @NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe memory m q ns frameBase stride inputBase outputBase hq hQ hA
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04
open TensorFormat
open NLA.Computation.SVDMachine
example {Caller : Program}
    (E : NLA.Proofs.TR04.RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (m :: ns)) (hA : StoresTensor memory inputBase (m :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * stride) outputBase (q * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (m * suffixSize ns) outputBase (q * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (contractMultiplyData memory m q ns frameBase stride inputBase outputBase) 0 scratch) (trace.state offset)) :
    let p := contractMultiplyData memory m q ns frameBase stride inputBase outputBase
    let n := offset + matrixMultiplyReturnTime p
    (trace.state n).label = E.labels 21 ∧ (trace.state n).status = .running ∧
      StoresTensor (trace.state n).memory outputBase (q :: ns) (contract Q A) ∧
      StoresTensor (trace.state n).memory inputBase (m :: ns) A ∧
      StoresFrame (trace.state n).memory frameBase stride Q ∧
      (∀ address, ¬ (outputBase ≤ address ∧ address < outputBase + q * suffixSize ns) →
        (trace.state n).memory address = memory address) ∧
      CostThrough Caller trace n ≤ CostThrough Caller trace offset + 17 * (q + m + suffixSize ns + 1)^3 ∧
      (∀ j : Fin Caller.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state n).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Caller.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state n).natural j = (trace.state offset).natural j) := @NLA.Proofs.TR04.RoutineEmbedding.contract_run_at Caller E m q ns memory frameBase stride inputBase outputBase hq Q hQ A hA hQblock hAblock scratch start trace ht offset hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open TensorFormat
open NLA.Computation.SVDMachine
example {Caller : Program}
    (E : NLA.Proofs.TR04.RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (q :: ns)) (hA : StoresTensor memory inputBase (q :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * stride) outputBase (m * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (q * suffixSize ns) outputBase (m * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (liftMultiplyData memory m q ns frameBase stride inputBase outputBase) 0 scratch) (trace.state offset)) :
    let p := liftMultiplyData memory m q ns frameBase stride inputBase outputBase
    let n := offset + matrixMultiplyReturnTime p
    (trace.state n).label = E.labels 21 ∧ (trace.state n).status = .running ∧
      StoresTensor (trace.state n).memory outputBase (m :: ns) (lift Q A) ∧
      StoresTensor (trace.state n).memory inputBase (q :: ns) A ∧
      StoresFrame (trace.state n).memory frameBase stride Q ∧
      (∀ address, ¬ (outputBase ≤ address ∧ address < outputBase + m * suffixSize ns) →
        (trace.state n).memory address = memory address) ∧
      CostThrough Caller trace n ≤ CostThrough Caller trace offset + 17 * (m + q + suffixSize ns + 1)^3 ∧
      (∀ j : Fin Caller.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state n).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Caller.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state n).natural j = (trace.state offset).natural j) := @NLA.Proofs.TR04.RoutineEmbedding.lift_run_at Caller E m q ns memory frameBase stride inputBase outputBase hq Q hQ A hA hQblock hAblock scratch start trace ht offset hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open TensorFormat
/-- A prefix retained in the full U array uses physical row stride m. -/
example {Caller : Program} (E : RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase inputBase outputBase : ℕ) (hq : q ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) (hU : readMatrix memory m m frameBase = U)
    (A : Tensor (m :: ns)) (hA : StoresTensor memory inputBase (m :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * m) outputBase (q * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (m * suffixSize ns) outputBase (q * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (contractMultiplyData memory m q ns frameBase m inputBase outputBase) 0 scratch) (trace.state offset)) :
    StoresTensor (trace.state (offset + matrixMultiplyReturnTime
      (contractMultiplyData memory m q ns frameBase m inputBase outputBase))).memory
        outputBase (q :: ns) (contract (U.submatrix id (Fin.castLE hq)) A) := by
  have H := E.contract_run_at memory frameBase m inputBase outputBase hq
    (U.submatrix id (Fin.castLE hq)) (storesFrame_prefix memory frameBase U hq hU)
    A hA hQblock hAblock scratch ht offset hs
  exact H.2.2.1

/-- A separately stored dense Q frame instead has physical row stride q. -/
example {Caller : Program} (E : RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase inputBase outputBase : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : readMatrix memory m q frameBase = Q)
    (A : Tensor (q :: ns)) (hA : StoresTensor memory inputBase (q :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * q) outputBase (m * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (q * suffixSize ns) outputBase (m * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (liftMultiplyData memory m q ns frameBase q inputBase outputBase) 0 scratch) (trace.state offset)) :
    StoresTensor (trace.state (offset + matrixMultiplyReturnTime
      (liftMultiplyData memory m q ns frameBase q inputBase outputBase))).memory outputBase (m :: ns) (lift Q A) := by
  have H := E.lift_run_at memory frameBase q inputBase outputBase le_rfl Q
    ((storesFrame_dense_iff memory frameBase Q).mpr hQ) A hA hQblock hAblock scratch ht offset hs
  exact H.2.2.1
end NLA.Proofs.TR04

end
