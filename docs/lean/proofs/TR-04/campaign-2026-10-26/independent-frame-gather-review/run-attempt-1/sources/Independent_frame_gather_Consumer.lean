import NLA.Proofs.TR04.MachineFrameGatherSVD

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
#assert_kind NLA.Proofs.TR04.FrameGatherParameters "inductive"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters
#print axioms NLA.Proofs.TR04.FrameGatherParameters
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.width "definition"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.width
#print axioms NLA.Proofs.TR04.FrameGatherParameters.width
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.Valid "inductive"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.Valid
#print axioms NLA.Proofs.TR04.FrameGatherParameters.Valid
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.counter "definition"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.column "definition"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.column
#print axioms NLA.Proofs.TR04.FrameGatherParameters.column
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.sourceAddress "definition"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.sourceAddress
#print axioms NLA.Proofs.TR04.FrameGatherParameters.sourceAddress
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le
#print axioms NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.counter_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter_prefix
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter_prefix
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.counter_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter_lt
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter_lt
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.counter_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter_succ
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter_succ
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.column_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.column_lt
#print axioms NLA.Proofs.TR04.FrameGatherParameters.column_lt
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat
#print axioms NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat
#assert_kind NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_mem "theorem"
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_mem
#print axioms NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_mem
#assert_kind NLA.Proofs.TR04.frameGatherMemory "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory
#print axioms NLA.Proofs.TR04.frameGatherMemory
#assert_kind NLA.Proofs.TR04.frameGatherMemory_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_zero
#print axioms NLA.Proofs.TR04.frameGatherMemory_zero
#assert_kind NLA.Proofs.TR04.frameGatherMemory_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_outside
#print axioms NLA.Proofs.TR04.frameGatherMemory_outside
#assert_kind NLA.Proofs.TR04.frameGatherMemory_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_succ
#print axioms NLA.Proofs.TR04.frameGatherMemory_succ
#assert_kind NLA.Proofs.TR04.frameGatherMemory_input "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_input
#print axioms NLA.Proofs.TR04.frameGatherMemory_input
#assert_kind NLA.Proofs.TR04.frameGatherMemory_read "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_read
#print axioms NLA.Proofs.TR04.frameGatherMemory_read
#assert_kind NLA.Proofs.TR04.frameGatherMemory_output "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_output
#print axioms NLA.Proofs.TR04.frameGatherMemory_output
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
#assert_kind NLA.Proofs.TR04.frameGatherProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram
#print axioms NLA.Proofs.TR04.frameGatherProgram
#assert_kind NLA.Proofs.TR04.frameGatherOuterState "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherOuterState
#print axioms NLA.Proofs.TR04.frameGatherOuterState
#assert_kind NLA.Proofs.TR04.frameGatherStart "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherStart
#print axioms NLA.Proofs.TR04.frameGatherStart
#assert_kind NLA.Proofs.TR04.frameGatherInnerState "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherInnerState
#print axioms NLA.Proofs.TR04.frameGatherInnerState
#assert_kind NLA.Proofs.TR04.frameGatherProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_scalar
#print axioms NLA.Proofs.TR04.frameGatherProgram_scalar
#assert_kind NLA.Proofs.TR04.frameGatherProgram_initialize "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_initialize
#print axioms NLA.Proofs.TR04.frameGatherProgram_initialize
#assert_kind NLA.Proofs.TR04.frameGatherProgram_row_setup "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_row_setup
#print axioms NLA.Proofs.TR04.frameGatherProgram_row_setup
#assert_kind NLA.Proofs.TR04.frameGatherProgram_eleven_steps "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_eleven_steps
#print axioms NLA.Proofs.TR04.frameGatherProgram_eleven_steps
#assert_kind NLA.Proofs.TR04.frameGatherProgram_inner_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_inner_iterations
#print axioms NLA.Proofs.TR04.frameGatherProgram_inner_iterations
#assert_kind NLA.Proofs.TR04.frameGatherProgram_row_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_row_exit
#print axioms NLA.Proofs.TR04.frameGatherProgram_row_exit
#assert_kind NLA.Proofs.TR04.frameGatherProgram_one_row "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_one_row
#print axioms NLA.Proofs.TR04.frameGatherProgram_one_row
#assert_kind NLA.Proofs.TR04.frameGatherProgram_rows "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_rows
#print axioms NLA.Proofs.TR04.frameGatherProgram_rows
#assert_kind NLA.Proofs.TR04.frameGatherReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherReturnState
#print axioms NLA.Proofs.TR04.frameGatherReturnState
#assert_kind NLA.Proofs.TR04.frameGatherProgram_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_return
#print axioms NLA.Proofs.TR04.frameGatherProgram_return
#assert_kind NLA.Proofs.TR04.frameGatherProgram_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_trace_result
#print axioms NLA.Proofs.TR04.frameGatherProgram_trace_result
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.frameGather_run "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_at
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells
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
#assert_kind NLA.Proofs.TR04.SVD.singularSubspace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace
#print axioms NLA.Proofs.TR04.SVD.singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.singularSubspace_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_le
#print axioms NLA.Proofs.TR04.SVD.singularSubspace_le
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le
#print axioms NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le
#assert_kind NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual
#print axioms NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_matrixColumns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_matrixColumns
#print axioms NLA.Proofs.TR04.SVD.orthonormal_matrixColumns
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections
#print axioms NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections
#assert_kind NLA.Proofs.TR04.SVD.finrank_singularSubspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.finrank_singularSubspace
#print axioms NLA.Proofs.TR04.SVD.finrank_singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.starProjection_singularSubspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.starProjection_singularSubspace
#print axioms NLA.Proofs.TR04.SVD.starProjection_singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace
#print axioms NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.validSVD_selected_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_selected_energy
#print axioms NLA.Proofs.TR04.SVD.validSVD_selected_energy
#assert_kind NLA.Proofs.TR04.SVD.validSVD_selected_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_selected_error
#print axioms NLA.Proofs.TR04.SVD.validSVD_selected_error
#assert_kind NLA.Proofs.TR04.SVD.cyclicWindow "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicWindow
#print axioms NLA.Proofs.TR04.SVD.cyclicWindow
#assert_kind NLA.Proofs.TR04.SVD.cyclicTranslate "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicTranslate
#print axioms NLA.Proofs.TR04.SVD.cyclicTranslate
#assert_kind NLA.Proofs.TR04.SVD.cyclicDifference "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicDifference
#print axioms NLA.Proofs.TR04.SVD.cyclicDifference
#assert_kind NLA.Proofs.TR04.SVD.prefixSubtypeEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixSubtypeEquiv
#print axioms NLA.Proofs.TR04.SVD.prefixSubtypeEquiv
#assert_kind NLA.Proofs.TR04.SVD.card_cyclicWindow "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.card_cyclicWindow
#print axioms NLA.Proofs.TR04.SVD.card_cyclicWindow
#assert_kind NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator
#print axioms NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator
#assert_kind NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy
#print axioms NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy
#assert_kind NLA.Proofs.TR04.SVD.average_cyclicWindow_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.average_cyclicWindow_energy
#print axioms NLA.Proofs.TR04.SVD.average_cyclicWindow_energy
#assert_kind NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average
#print axioms NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average
#assert_kind NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal
#print axioms NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.norm_singularSubspace_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_singularSubspace_projection
#print axioms NLA.Proofs.TR04.SVD.norm_singularSubspace_projection
#assert_kind NLA.Proofs.TR04.SVD.singularCoordinateEnergy "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularCoordinateEnergy
#print axioms NLA.Proofs.TR04.SVD.singularCoordinateEnergy
#assert_kind NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg
#print axioms NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg
#assert_kind NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy
#print axioms NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy
#assert_kind NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le
#print axioms NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le
#assert_kind NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns
#print axioms NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns
#assert_kind NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le
#print axioms NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le
#assert_kind NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank
#print axioms NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank
#assert_kind NLA.Proofs.TR04.SVD.rank_selected_projection_le_card "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_selected_projection_le_card
#print axioms NLA.Proofs.TR04.SVD.rank_selected_projection_le_card
#assert_kind NLA.Proofs.TR04.SVD.selectedFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.selectedFrame
#print axioms NLA.Proofs.TR04.SVD.selectedFrame
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_rank
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_rank
#assert_kind NLA.Proofs.TR04.SVD.rank_selectedFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_selectedFrame
#print axioms NLA.Proofs.TR04.SVD.rank_selectedFrame
#assert_kind NLA.Proofs.TR04.SVD.tieEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieEmbedding
#print axioms NLA.Proofs.TR04.SVD.tieEmbedding
#assert_kind NLA.Proofs.TR04.SVD.tieEmbedding_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieEmbedding_injective
#print axioms NLA.Proofs.TR04.SVD.tieEmbedding_injective
#assert_kind NLA.Proofs.TR04.SVD.prefixDirections "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixDirections
#print axioms NLA.Proofs.TR04.SVD.prefixDirections
#assert_kind NLA.Proofs.TR04.SVD.tieDirections "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieDirections
#print axioms NLA.Proofs.TR04.SVD.tieDirections
#assert_kind NLA.Proofs.TR04.SVD.windowDirections "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.windowDirections
#print axioms NLA.Proofs.TR04.SVD.windowDirections
#assert_kind NLA.Proofs.TR04.SVD.tieSelection "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieSelection
#print axioms NLA.Proofs.TR04.SVD.tieSelection
#assert_kind NLA.Proofs.TR04.SVD.prefix_window_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_window_disjoint
#print axioms NLA.Proofs.TR04.SVD.prefix_window_disjoint
#assert_kind NLA.Proofs.TR04.SVD.card_tieSelection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.card_tieSelection
#print axioms NLA.Proofs.TR04.SVD.card_tieSelection
#assert_kind NLA.Proofs.TR04.SVD.sum_tieSelection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection
#print axioms NLA.Proofs.TR04.SVD.sum_tieSelection
#assert_kind NLA.Proofs.TR04.SVD.sum_all_tieSelections "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_all_tieSelections
#print axioms NLA.Proofs.TR04.SVD.sum_all_tieSelections
#assert_kind NLA.Proofs.TR04.SVD.sum_indicator_finset "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_indicator_finset
#print axioms NLA.Proofs.TR04.SVD.sum_indicator_finset
#assert_kind NLA.Proofs.TR04.SVD.directionSubspace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.directionSubspace
#print axioms NLA.Proofs.TR04.SVD.directionSubspace
#assert_kind NLA.Proofs.TR04.SVD.directionSubspace_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.directionSubspace_project_energy
#print axioms NLA.Proofs.TR04.SVD.directionSubspace_project_energy
#assert_kind NLA.Proofs.TR04.SVD.rank_directionFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_directionFrame
#print axioms NLA.Proofs.TR04.SVD.rank_directionFrame
#assert_kind NLA.Proofs.TR04.SVD.rank_directionProjection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_directionProjection_le
#print axioms NLA.Proofs.TR04.SVD.rank_directionProjection_le
#assert_kind NLA.Proofs.TR04.SVD.rank_tieSelectionFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_tieSelectionFrame
#print axioms NLA.Proofs.TR04.SVD.rank_tieSelectionFrame
#assert_kind NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le
#print axioms NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le
#assert_kind NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy
#print axioms NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy
#assert_kind NLA.Proofs.TR04.SVD.average_tieSelection_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.average_tieSelection_project_energy
#print axioms NLA.Proofs.TR04.SVD.average_tieSelection_project_energy
#assert_kind NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le
#print axioms NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le
#assert_kind NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le
#print axioms NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le
#assert_kind NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin
#print axioms NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin
#assert_kind NLA.Proofs.TR04.SVD.sum_prefixDirections "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_prefixDirections
#print axioms NLA.Proofs.TR04.SVD.sum_prefixDirections
#assert_kind NLA.Proofs.TR04.SVD.prefixEnergy_tie_split "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy_tie_split
#print axioms NLA.Proofs.TR04.SVD.prefixEnergy_tie_split
#assert_kind NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block
#print axioms NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block
#assert_kind NLA.Proofs.TR04.SVD.validSVD_tieSelection_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_tieSelection_error
#print axioms NLA.Proofs.TR04.SVD.validSVD_tieSelection_error
#assert_kind NLA.Proofs.TR04.SVD.card_filter_fin_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.card_filter_fin_lt
#print axioms NLA.Proofs.TR04.SVD.card_filter_fin_lt
#assert_kind NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card
#print axioms NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card
#assert_kind NLA.Proofs.TR04.SVD.TieStructure "inductive"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure
#print axioms NLA.Proofs.TR04.SVD.TieStructure
#assert_kind NLA.Proofs.TR04.SVD.exists_tieStructure "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_tieStructure
#print axioms NLA.Proofs.TR04.SVD.exists_tieStructure
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.tied_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.tied_pos
#print axioms NLA.Proofs.TR04.SVD.TieStructure.tied_pos
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equal_embedding "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equal_embedding
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equal_embedding
#assert_kind NLA.Proofs.TR04.SVD.mem_prefixDirections_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.mem_prefixDirections_iff
#print axioms NLA.Proofs.TR04.SVD.mem_prefixDirections_iff
#assert_kind NLA.Proofs.TR04.SVD.tieSelection_val_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieSelection_val_lt
#print axioms NLA.Proofs.TR04.SVD.tieSelection_val_lt
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.above_subspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.above_subspace
#print axioms NLA.Proofs.TR04.SVD.TieStructure.above_subspace
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.first_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.first_error
#print axioms NLA.Proofs.TR04.SVD.TieStructure.first_error
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.frame_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.frame_rank
#print axioms NLA.Proofs.TR04.SVD.TieStructure.frame_rank
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual
#assert_kind NLA.Proofs.TR04.SVD.prefix_weights_eq_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_weights_eq_one
#print axioms NLA.Proofs.TR04.SVD.prefix_weights_eq_one
#assert_kind NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights
#print axioms NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero
#print axioms NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual
#assert_kind NLA.Proofs.TR04.SVD.starProjection_span_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.starProjection_span_orthonormal
#print axioms NLA.Proofs.TR04.SVD.starProjection_span_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.frameSpace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.frameSpace
#print axioms NLA.Proofs.TR04.SVD.frameSpace
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_frameColumns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_frameColumns
#print axioms NLA.Proofs.TR04.SVD.orthonormal_frameColumns
#assert_kind NLA.Proofs.TR04.SVD.frame_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.frame_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.frame_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.exists_directionFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_directionFrame
#print axioms NLA.Proofs.TR04.SVD.exists_directionFrame
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.exists_frame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.exists_frame
#print axioms NLA.Proofs.TR04.SVD.TieStructure.exists_frame
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_val
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_val
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_space "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_space
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_space
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_rank
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_rank
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_projection
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_projection
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure_above "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_above
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_above
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure_tied "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_tied
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_tied
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure_take "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_take
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_take
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank
#assert_kind NLA.Proofs.TR04.frameGatherMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMatrix
#print axioms NLA.Proofs.TR04.frameGatherMatrix
#assert_kind NLA.Proofs.TR04.frameGatherMemory_matrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_matrix
#print axioms NLA.Proofs.TR04.frameGatherMemory_matrix
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix
#assert_kind NLA.Proofs.TR04.tieGatherParameters "definition"
#assert_trust kernel NLA.Proofs.TR04.tieGatherParameters
#print axioms NLA.Proofs.TR04.tieGatherParameters
#assert_kind NLA.Proofs.TR04.tieGatherParameters_valid "theorem"
#assert_trust kernel NLA.Proofs.TR04.tieGatherParameters_valid
#print axioms NLA.Proofs.TR04.tieGatherParameters_valid
#assert_kind NLA.Proofs.TR04.tieGatherParameters_width "theorem"
#assert_trust kernel NLA.Proofs.TR04.tieGatherParameters_width
#print axioms NLA.Proofs.TR04.tieGatherParameters_width
#assert_kind NLA.Proofs.TR04.frameGatherMatrix_tie "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMatrix_tie
#print axioms NLA.Proofs.TR04.frameGatherMatrix_tie
#assert_kind NLA.Proofs.TR04.prefixGatherParameters "definition"
#assert_trust kernel NLA.Proofs.TR04.prefixGatherParameters
#print axioms NLA.Proofs.TR04.prefixGatherParameters
#assert_kind NLA.Proofs.TR04.prefixGatherParameters_valid "theorem"
#assert_trust kernel NLA.Proofs.TR04.prefixGatherParameters_valid
#print axioms NLA.Proofs.TR04.prefixGatherParameters_valid
#assert_kind NLA.Proofs.TR04.frameGatherMatrix_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.frameGatherMatrix_prefix
#print axioms NLA.Proofs.TR04.frameGatherMatrix_prefix

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {P : FrameGatherParameters} (hP : P.Valid) :
    P.width ≤ P.rows := @NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le P hP
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {P : FrameGatherParameters} (hP : P.Valid)
    (k : ℕ) (hk : k < P.width) : P.column k < P.rows := @NLA.Proofs.TR04.FrameGatherParameters.column_lt P hP k hk
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (P : FrameGatherParameters)
    (i k : ℕ) (hk : k < P.width) :
    P.sourceAddress (i * P.width + k) = P.inputBase + i * P.rows + P.column k := @NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat P i k hk
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ) :
    (ordinaryStep frameGatherProgram)^[3]
      (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) =
        frameGatherOuterState memory P 0 aux value := @NLA.Proofs.TR04.frameGatherProgram_initialize memory P aux rowScratch widthScratch writeScratch value
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (i k selected address : ℕ) (value : ℝ) (hi : i < P.rows) (hk : k < P.width) :
    (ordinaryStep frameGatherProgram)^[11] (frameGatherInnerState memory P i k selected address value) =
      frameGatherInnerState memory P i (k + 1) (P.column k) (P.sourceAddress (i * P.width + k))
        (memory (P.sourceAddress (i * P.width + k))) := @NLA.Proofs.TR04.frameGatherProgram_eleven_steps memory P hP hd i k selected address value hi hk
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    (trace : Trace frameGatherProgram)
    (ht : LegalTrace frameGatherProgram
      (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) trace) :
    (trace.state (P.rows * (11 * P.width + 7) + 5)).status = .halted P.outputBase ∧
      (trace.state (P.rows * (11 * P.width + 7) + 5)).memory =
        frameGatherMemory memory P (P.rows * P.width) ∧
      CostThrough frameGatherProgram trace (P.rows * (11 * P.width + 7) + 5) ≤
        P.rows * (11 * P.width + 7) + 5 := @NLA.Proofs.TR04.frameGatherProgram_trace_result memory P hP hd aux rowScratch widthScratch writeScratch value trace ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    let n := offset + (P.rows * (11 * P.width + 7) + 4)
    (trace.state n).label = E.labels 25 ∧ (trace.state n).status = .running ∧
      (∀ i < P.rows, ∀ k < P.width,
        (trace.state n).memory (P.outputBase + i * P.width + k) =
          memory (P.inputBase + i * P.rows + P.column k)) ∧
      (∀ a, ¬ (P.outputBase ≤ a ∧ a < P.outputBase + P.rows * P.width) →
        (trace.state n).memory a = memory a) ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (P.rows * (11 * P.width + 7) + 4) := @NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells Q E memory P hP hd aux rowScratch widthScratch writeScratch value start trace offset hs ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (U : Matrix (Fin P.rows) (Fin P.rows) ℝ)
    (hU : ∀ i j, memory (P.inputBase + i.val * P.rows + j.val) = U i j)
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    ∀ i : Fin P.rows, ∀ k : Fin P.width,
      (trace.state (offset + (P.rows * (11 * P.width + 7) + 4))).memory
          (P.outputBase + i.val * P.width + k.val) = frameGatherMatrix P hP U i k := @NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix Q E memory P hP hd U hU aux rowScratch widthScratch writeScratch value start trace offset hs ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ) :
    (tieGatherParameters T j inputBase outputBase).Valid := @NLA.Proofs.TR04.tieGatherParameters_valid m l sigma a T j inputBase outputBase
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ) :
    (tieGatherParameters T j inputBase outputBase).width = a.val + 1 := @NLA.Proofs.TR04.tieGatherParameters_width m l sigma a T j inputBase outputBase
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    (frameGatherMatrix (tieGatherParameters T j inputBase outputBase)
      (tieGatherParameters_valid T j inputBase outputBase) U).submatrix id (Fin.cast T.rank_eq.symm) =
        T.explicitFrame U j := @NLA.Proofs.TR04.frameGatherMatrix_tie m l sigma a T j inputBase outputBase U
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (m width inputBase outputBase : ℕ) (hw : width ≤ m) :
    (prefixGatherParameters m width inputBase outputBase).Valid := @NLA.Proofs.TR04.prefixGatherParameters_valid m width inputBase outputBase hw
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (m width inputBase outputBase : ℕ) (hw : width ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    frameGatherMatrix (prefixGatherParameters m width inputBase outputBase)
      (prefixGatherParameters_valid m width inputBase outputBase hw) U = U.submatrix id (Fin.castLE hw) := @NLA.Proofs.TR04.frameGatherMatrix_prefix m width inputBase outputBase hw U
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
/-- Actual caller trace readback is the literal explicit cyclic SVD frame. -/
example {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ)
    (memory : ℕ → ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (hU : ∀ i k, memory (inputBase + i.val * m + k.val) = U i k)
    (hd : DisjointBlocks inputBase (m * m) outputBase (m * (T.above + T.take)))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory (tieGatherParameters T j inputBase outputBase)
      aux rowScratch widthScratch writeScratch value) (trace.state offset))
    (ht : LegalTrace Q start trace) :
    ∀ i : Fin m, ∀ k : Fin (T.above + T.take),
      (trace.state (offset + (m * (11 * (T.above + T.take) + 7) + 4))).memory
        (outputBase + i.val * (T.above + T.take) + k.val) =
          T.explicitFrame U j i (Fin.cast T.rank_eq k) := by
  have H := E.frameGather_run_matrix memory (tieGatherParameters T j inputBase outputBase)
    (tieGatherParameters_valid T j inputBase outputBase) hd U hU aux
    rowScratch widthScratch writeScratch value offset hs ht
  intro i k
  have hc := H i k
  have hf := congrArg (fun M => M i (Fin.cast T.rank_eq k))
    (frameGatherMatrix_tie T j inputBase outputBase U)
  change frameGatherMatrix (tieGatherParameters T j inputBase outputBase)
    (tieGatherParameters_valid T j inputBase outputBase) U i
      (Fin.cast T.rank_eq.symm (Fin.cast T.rank_eq k)) = _ at hf
  have hk : Fin.cast T.rank_eq.symm (Fin.cast T.rank_eq k) = k := Fin.ext rfl
  rw [hk] at hf
  exact hc.trans hf

/-- Actual caller trace readback is the literal prefix U frame, including width0. -/
example {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (m width inputBase outputBase : ℕ) (hw : width ≤ m)
    (memory : ℕ → ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (hU : ∀ i k, memory (inputBase + i.val * m + k.val) = U i k)
    (hd : DisjointBlocks inputBase (m * m) outputBase (m * width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory (prefixGatherParameters m width inputBase outputBase)
      aux rowScratch widthScratch writeScratch value) (trace.state offset))
    (ht : LegalTrace Q start trace) :
    ∀ i : Fin m, ∀ k : Fin width,
      (trace.state (offset + (m * (11 * width + 7) + 4))).memory
        (outputBase + i.val * width + k.val) = U i (Fin.castLE hw k) := by
  have H := E.frameGather_run_matrix memory (prefixGatherParameters m width inputBase outputBase)
    (prefixGatherParameters_valid m width inputBase outputBase hw) hd U hU aux
    rowScratch widthScratch writeScratch value offset hs ht
  rw [frameGatherMatrix_prefix m width inputBase outputBase hw U] at H
  simpa only [prefixGatherParameters, FrameGatherParameters.width, Nat.add_zero, Matrix.submatrix] using H
end NLA.Proofs.TR04

end
