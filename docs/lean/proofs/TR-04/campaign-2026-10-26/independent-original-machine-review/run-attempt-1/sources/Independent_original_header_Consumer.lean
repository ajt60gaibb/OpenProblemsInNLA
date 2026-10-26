import NLA.Proofs.TR04.MachineHeaderProductOriginal

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
#assert_kind NLA.Proofs.TR04.shapeHeaderValues "definition"
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues
#print axioms NLA.Proofs.TR04.shapeHeaderValues
#assert_kind NLA.Proofs.TR04.shapeHeaderValues_fin "theorem"
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues_fin
#print axioms NLA.Proofs.TR04.shapeHeaderValues_fin
#assert_kind NLA.Proofs.TR04.inputMemory_shapeHeader "theorem"
#assert_trust kernel NLA.Proofs.TR04.inputMemory_shapeHeader
#print axioms NLA.Proofs.TR04.inputMemory_shapeHeader
#assert_kind NLA.Proofs.TR04.shapeHeaderValues_sum "theorem"
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues_sum
#print axioms NLA.Proofs.TR04.shapeHeaderValues_sum
#assert_kind NLA.Proofs.TR04.shapeHeaderValues_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues_product
#print axioms NLA.Proofs.TR04.shapeHeaderValues_product
#assert_kind NLA.Proofs.TR04.fin_sum_le_prod_of_two_le_aux "theorem"
#assert_trust kernel NLA.Proofs.TR04.fin_sum_le_prod_of_two_le_aux
#print axioms NLA.Proofs.TR04.fin_sum_le_prod_of_two_le_aux
#assert_kind NLA.Proofs.TR04.fin_sum_le_prod_of_two_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.fin_sum_le_prod_of_two_le
#print axioms NLA.Proofs.TR04.fin_sum_le_prod_of_two_le
#assert_kind NLA.Proofs.TR04.shape_sum_modes_le_denseSize "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_sum_modes_le_denseSize
#print axioms NLA.Proofs.TR04.shape_sum_modes_le_denseSize
#assert_kind NLA.Proofs.TR04.shape_denseSize_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_denseSize_pos
#print axioms NLA.Proofs.TR04.shape_denseSize_pos
#assert_kind NLA.Proofs.TR04.shape_order_le_denseSize "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_order_le_denseSize
#print axioms NLA.Proofs.TR04.shape_order_le_denseSize
#assert_kind NLA.Proofs.TR04.shape_mode_le_denseSize "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_mode_le_denseSize
#print axioms NLA.Proofs.TR04.shape_mode_le_denseSize
#assert_kind NLA.Proofs.TR04.shape_suffix_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_suffix_pos
#print axioms NLA.Proofs.TR04.shape_suffix_pos
#assert_kind NLA.Proofs.TR04.shape_suffix_le_denseSize "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_suffix_le_denseSize
#print axioms NLA.Proofs.TR04.shape_suffix_le_denseSize
#assert_kind NLA.Proofs.TR04.shape_denseSize_le_size "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_denseSize_le_size
#print axioms NLA.Proofs.TR04.shape_denseSize_le_size
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
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside
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
#assert_kind NLA.Proofs.TR04.headerProductProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductProgram
#print axioms NLA.Proofs.TR04.headerProductProgram
#assert_kind NLA.Proofs.TR04.headerDecoderLabelMap "definition"
#assert_trust kernel NLA.Proofs.TR04.headerDecoderLabelMap
#print axioms NLA.Proofs.TR04.headerDecoderLabelMap
#assert_kind NLA.Proofs.TR04.headerDecoderNatMap "definition"
#assert_trust kernel NLA.Proofs.TR04.headerDecoderNatMap
#print axioms NLA.Proofs.TR04.headerDecoderNatMap
#assert_kind NLA.Proofs.TR04.headerDecoderEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.headerDecoderEmbedding
#print axioms NLA.Proofs.TR04.headerDecoderEmbedding
#assert_kind NLA.Proofs.TR04.headerPrefixProduct "definition"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixProduct
#print axioms NLA.Proofs.TR04.headerPrefixProduct
#assert_kind NLA.Proofs.TR04.headerPrefixTime "definition"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixTime
#print axioms NLA.Proofs.TR04.headerPrefixTime
#assert_kind NLA.Proofs.TR04.headerProductLoopState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductLoopState
#print axioms NLA.Proofs.TR04.headerProductLoopState
#assert_kind NLA.Proofs.TR04.headerProductDecodeState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductDecodeState
#print axioms NLA.Proofs.TR04.headerProductDecodeState
#assert_kind NLA.Proofs.TR04.headerProductProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProductProgram_scalar
#print axioms NLA.Proofs.TR04.headerProductProgram_scalar
#assert_kind NLA.Proofs.TR04.headerProduct_setup "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_setup
#print axioms NLA.Proofs.TR04.headerProduct_setup
#assert_kind NLA.Proofs.TR04.headerProduct_decode_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_decode_relates
#print axioms NLA.Proofs.TR04.headerProduct_decode_relates
#assert_kind NLA.Proofs.TR04.headerProductAfterDecode "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductAfterDecode
#print axioms NLA.Proofs.TR04.headerProductAfterDecode
#assert_kind NLA.Proofs.TR04.headerProduct_decode "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_decode
#print axioms NLA.Proofs.TR04.headerProduct_decode
#assert_kind NLA.Proofs.TR04.headerPrefixProduct_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixProduct_succ
#print axioms NLA.Proofs.TR04.headerPrefixProduct_succ
#assert_kind NLA.Proofs.TR04.headerPrefixTime_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixTime_succ
#print axioms NLA.Proofs.TR04.headerPrefixTime_succ
#assert_kind NLA.Proofs.TR04.headerProduct_finish "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_finish
#print axioms NLA.Proofs.TR04.headerProduct_finish
#assert_kind NLA.Proofs.TR04.headerProduct_iteration "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_iteration
#print axioms NLA.Proofs.TR04.headerProduct_iteration
#assert_kind NLA.Proofs.TR04.headerProduct_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_iterations
#print axioms NLA.Proofs.TR04.headerProduct_iterations
#assert_kind NLA.Proofs.TR04.headerProduct_initial "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_initial
#print axioms NLA.Proofs.TR04.headerProduct_initial
#assert_kind NLA.Proofs.TR04.headerProductFinalState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductFinalState
#print axioms NLA.Proofs.TR04.headerProductFinalState
#assert_kind NLA.Proofs.TR04.headerProduct_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_exit
#print axioms NLA.Proofs.TR04.headerProduct_exit
#assert_kind NLA.Proofs.TR04.headerProductTime "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductTime
#print axioms NLA.Proofs.TR04.headerProductTime
#assert_kind NLA.Proofs.TR04.headerProduct_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_trace_result
#print axioms NLA.Proofs.TR04.headerProduct_trace_result
#assert_kind NLA.Proofs.TR04.headerProduct_trace_cost "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_trace_cost
#print axioms NLA.Proofs.TR04.headerProduct_trace_cost
#assert_kind NLA.Proofs.TR04.headerPrefixProduct_shape "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixProduct_shape
#print axioms NLA.Proofs.TR04.headerPrefixProduct_shape
#assert_kind NLA.Proofs.TR04.headerPrefixProduct_shape_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixProduct_shape_le
#print axioms NLA.Proofs.TR04.headerPrefixProduct_shape_le
#assert_kind NLA.Proofs.TR04.headerPrefixTime_shape "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerPrefixTime_shape
#print axioms NLA.Proofs.TR04.headerPrefixTime_shape
#assert_kind NLA.Proofs.TR04.headerProductTime_shape "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProductTime_shape
#print axioms NLA.Proofs.TR04.headerProductTime_shape
#assert_kind NLA.Proofs.TR04.headerProductTime_shape_le_size "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProductTime_shape_le_size
#print axioms NLA.Proofs.TR04.headerProductTime_shape_le_size
#assert_kind NLA.Proofs.TR04.shape_headerProduct_trace_exists "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_headerProduct_trace_exists
#print axioms NLA.Proofs.TR04.shape_headerProduct_trace_exists
#assert_kind NLA.Proofs.TR04.shape_headerProduct_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.shape_headerProduct_trace_result
#print axioms NLA.Proofs.TR04.shape_headerProduct_trace_result

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (A : Tensor S)
    (j : ℕ) (hj : j < S.order) :
    InputMemory S r A j = (shapeHeaderValues S j : ℝ) := @NLA.Proofs.TR04.inputMemory_shapeHeader S r A j hj
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation
example (S : Shape) :
    (∏ j ∈ Finset.range S.order, shapeHeaderValues S j) = DenseSize S := @NLA.Proofs.TR04.shapeHeaderValues_product S
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation
example (S : Shape) :
    (∑ i, S.mode i) ≤ DenseSize S := @NLA.Proofs.TR04.shape_sum_modes_le_denseSize S
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (i : Fin S.order) :
    SuffixSize S i ≤ DenseSize S := @NLA.Proofs.TR04.shape_suffix_le_denseSize S i
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (i : ℕ) (hi : i ≤ S.order) :
    headerPrefixProduct (shapeHeaderValues S) i ≤ DenseSize S := @NLA.Proofs.TR04.headerPrefixProduct_shape_le S i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) :
    headerProductTime (shapeHeaderValues S) S.order ≤ 7 * Size S r := @NLA.Proofs.TR04.headerProductTime_shape_le_size S r
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ trace : Trace headerProductProgram,
      LegalTrace headerProductProgram (Start headerProductProgram S r A) trace := @NLA.Proofs.TR04.shape_headerProduct_trace_exists S r A
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace headerProductProgram)
    (ht : LegalTrace headerProductProgram (Start headerProductProgram S r A) trace) :
    (trace.state (headerProductTime (shapeHeaderValues S) S.order)).natural 2 = DenseSize S ∧
    (trace.state (headerProductTime (shapeHeaderValues S) S.order)).status = .halted (DenseSize S) ∧
    (trace.state (headerProductTime (shapeHeaderValues S) S.order)).memory = InputMemory S r A ∧
    CostThrough headerProductProgram trace (headerProductTime (shapeHeaderValues S) S.order) ≤
      7 * Size S r := @NLA.Proofs.TR04.shape_headerProduct_trace_result S r A trace ht
end NLA.Proofs.TR04
end
