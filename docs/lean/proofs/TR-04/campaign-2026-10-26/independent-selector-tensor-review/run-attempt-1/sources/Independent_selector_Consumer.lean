import NLA.Proofs.TR04.MachineBestCandidateCallable

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
#assert_kind NLA.Proofs.TR04.squaredErrorProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram
#print axioms NLA.Proofs.TR04.squaredErrorProgram
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters
#assert_kind NLA.Proofs.TR04.squaredErrorSum "definition"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum
#print axioms NLA.Proofs.TR04.squaredErrorSum
#assert_kind NLA.Proofs.TR04.squaredErrorSum_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum_zero
#print axioms NLA.Proofs.TR04.squaredErrorSum_zero
#assert_kind NLA.Proofs.TR04.squaredErrorSum_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorSum_succ
#print axioms NLA.Proofs.TR04.squaredErrorSum_succ
#assert_kind NLA.Proofs.TR04.squaredErrorLoopState "definition"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorLoopState
#print axioms NLA.Proofs.TR04.squaredErrorLoopState
#assert_kind NLA.Proofs.TR04.squaredErrorStart "definition"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorStart
#print axioms NLA.Proofs.TR04.squaredErrorStart
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_scalar
#print axioms NLA.Proofs.TR04.squaredErrorProgram_scalar
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_initialize "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_initialize
#print axioms NLA.Proofs.TR04.squaredErrorProgram_initialize
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_nine_steps "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nine_steps
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nine_steps
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_iterations
#print axioms NLA.Proofs.TR04.squaredErrorProgram_iterations
#assert_kind NLA.Proofs.TR04.squaredErrorFinalState "definition"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorFinalState
#print axioms NLA.Proofs.TR04.squaredErrorFinalState
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_exit
#print axioms NLA.Proofs.TR04.squaredErrorProgram_exit
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_finish "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_finish
#print axioms NLA.Proofs.TR04.squaredErrorProgram_finish
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_trace_result
#print axioms NLA.Proofs.TR04.squaredErrorProgram_trace_result
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_trace_cost "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_trace_cost
#print axioms NLA.Proofs.TR04.squaredErrorProgram_trace_cost
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_nohalt_phase "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nohalt_phase
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nohalt_phase
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_nohalt_loop_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nohalt_loop_prefix
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nohalt_loop_prefix
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_nohalt_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_nohalt_prefix
#print axioms NLA.Proofs.TR04.squaredErrorProgram_nohalt_prefix
#assert_kind NLA.Proofs.TR04.squaredErrorReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorReturnState
#print axioms NLA.Proofs.TR04.squaredErrorReturnState
#assert_kind NLA.Proofs.TR04.squaredErrorProgram_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.squaredErrorProgram_return
#print axioms NLA.Proofs.TR04.squaredErrorProgram_return
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.squaredError_run "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_at
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_value "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_value
#print axioms NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_value
#assert_kind NLA.Proofs.TR04.BestCandidateData "inductive"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData
#print axioms NLA.Proofs.TR04.BestCandidateData
#assert_kind NLA.Proofs.TR04.BestCandidateData.candidateBase "definition"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.candidateBase
#print axioms NLA.Proofs.TR04.BestCandidateData.candidateBase
#assert_kind NLA.Proofs.TR04.BestCandidateData.candidateError "definition"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.candidateError
#print axioms NLA.Proofs.TR04.BestCandidateData.candidateError
#assert_kind NLA.Proofs.TR04.BestCandidateData.MinimumSoFar "definition"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.MinimumSoFar
#print axioms NLA.Proofs.TR04.BestCandidateData.MinimumSoFar
#assert_kind NLA.Proofs.TR04.BestCandidateData.minimum_take "theorem"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.minimum_take
#print axioms NLA.Proofs.TR04.BestCandidateData.minimum_take
#assert_kind NLA.Proofs.TR04.BestCandidateData.minimum_keep "theorem"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateData.minimum_keep
#print axioms NLA.Proofs.TR04.BestCandidateData.minimum_keep
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside
#assert_kind NLA.Proofs.TR04.bestCandidateProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram
#print axioms NLA.Proofs.TR04.bestCandidateProgram
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters
#print axioms NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters
#assert_kind NLA.Proofs.TR04.bestCandidateErrorLabels "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorLabels
#print axioms NLA.Proofs.TR04.bestCandidateErrorLabels
#assert_kind NLA.Proofs.TR04.bestCandidateErrorNaturals "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorNaturals
#print axioms NLA.Proofs.TR04.bestCandidateErrorNaturals
#assert_kind NLA.Proofs.TR04.bestCandidateErrorReals "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorReals
#print axioms NLA.Proofs.TR04.bestCandidateErrorReals
#assert_kind NLA.Proofs.TR04.bestCandidateErrorEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorEmbedding
#print axioms NLA.Proofs.TR04.bestCandidateErrorEmbedding
#assert_kind NLA.Proofs.TR04.BestCandidateScratch "inductive"
#assert_trust kernel NLA.Proofs.TR04.BestCandidateScratch
#print axioms NLA.Proofs.TR04.BestCandidateScratch
#assert_kind NLA.Proofs.TR04.bestCandidateState "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateState
#print axioms NLA.Proofs.TR04.bestCandidateState
#assert_kind NLA.Proofs.TR04.bestCandidateLoopState "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateLoopState
#print axioms NLA.Proofs.TR04.bestCandidateLoopState
#assert_kind NLA.Proofs.TR04.bestCandidateErrorState "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateErrorState
#print axioms NLA.Proofs.TR04.bestCandidateErrorState
#assert_kind NLA.Proofs.TR04.bestCandidateAfterError "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateAfterError
#print axioms NLA.Proofs.TR04.bestCandidateAfterError
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_scalar
#print axioms NLA.Proofs.TR04.bestCandidateProgram_scalar
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_setup "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_setup
#print axioms NLA.Proofs.TR04.bestCandidateProgram_setup
#assert_kind NLA.Proofs.TR04.bestCandidate_error_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidate_error_relates
#print axioms NLA.Proofs.TR04.bestCandidate_error_relates
#assert_kind NLA.Proofs.TR04.bestCandidateResultScratch "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateResultScratch
#print axioms NLA.Proofs.TR04.bestCandidateResultScratch
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_first "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_first
#print axioms NLA.Proofs.TR04.bestCandidateProgram_first
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_take "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_take
#print axioms NLA.Proofs.TR04.bestCandidateProgram_take
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_keep "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_keep
#print axioms NLA.Proofs.TR04.bestCandidateProgram_keep
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_error
#print axioms NLA.Proofs.TR04.bestCandidateProgram_error
#assert_kind NLA.Proofs.TR04.bestCandidateIterationTime "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateIterationTime
#print axioms NLA.Proofs.TR04.bestCandidateIterationTime
#assert_kind NLA.Proofs.TR04.bestCandidateTime "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateTime
#print axioms NLA.Proofs.TR04.bestCandidateTime
#assert_kind NLA.Proofs.TR04.bestCandidateStart "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateStart
#print axioms NLA.Proofs.TR04.bestCandidateStart
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_initial "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_initial
#print axioms NLA.Proofs.TR04.bestCandidateProgram_initial
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_iteration "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_iteration
#print axioms NLA.Proofs.TR04.bestCandidateProgram_iteration
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_iterations
#print axioms NLA.Proofs.TR04.bestCandidateProgram_iterations
#assert_kind NLA.Proofs.TR04.bestCandidateFinalState "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateFinalState
#print axioms NLA.Proofs.TR04.bestCandidateFinalState
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_exit
#print axioms NLA.Proofs.TR04.bestCandidateProgram_exit
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_trace_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_trace_result
#print axioms NLA.Proofs.TR04.bestCandidateProgram_trace_result
#assert_kind NLA.Proofs.TR04.bestCandidateTime_le_polynomial "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateTime_le_polynomial
#print axioms NLA.Proofs.TR04.bestCandidateTime_le_polynomial
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_run "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_run
#print axioms NLA.Proofs.TR04.bestCandidateProgram_run
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_exists_trace "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_exists_trace
#print axioms NLA.Proofs.TR04.bestCandidateProgram_exists_trace
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
#assert_kind NLA.Proofs.TR04.bestCandidateReturnTime "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateReturnTime
#print axioms NLA.Proofs.TR04.bestCandidateReturnTime
#assert_kind NLA.Proofs.TR04.bestCandidateReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateReturnState
#print axioms NLA.Proofs.TR04.bestCandidateReturnState
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_return_step "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_return_step
#print axioms NLA.Proofs.TR04.bestCandidateProgram_return_step
#assert_kind NLA.Proofs.TR04.bestCandidateProgram_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateProgram_return
#print axioms NLA.Proofs.TR04.bestCandidateProgram_return
#assert_kind NLA.Proofs.TR04.bestCandidateReturnTime_le_polynomial "theorem"
#assert_trust kernel NLA.Proofs.TR04.bestCandidateReturnTime_le_polynomial
#print axioms NLA.Proofs.TR04.bestCandidateReturnTime_le_polynomial
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_run_at
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_value_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_value_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_value_at

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04

example (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (h : p.MinimumSoFar j winner value) (ht : j = 0 ∨ p.candidateError j < value) :
    p.MinimumSoFar (j + 1) j (p.candidateError j) := @NLA.Proofs.TR04.BestCandidateData.minimum_take p j winner value h ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04

example (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (h : p.MinimumSoFar j winner value) (hj : j ≠ 0) (ht : ¬ p.candidateError j < value) :
    p.MinimumSoFar (j + 1) winner value := @NLA.Proofs.TR04.BestCandidateData.minimum_keep p j winner value h hj ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (value : ℝ)
    (scratch : BestCandidateScratch) :
    (ordinaryStep bestCandidateProgram)^[2] (bestCandidateStart p value scratch) =
      bestCandidateLoopState p 0 0 value scratch := @NLA.Proofs.TR04.bestCandidateProgram_initial p value scratch
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (j winner : ℕ)
    (value : ℝ) (reals : Fin 3 → ℝ) :
    ∃ a b : ℝ, (ordinaryStep bestCandidateProgram)^[9 * p.entries + 2]
      (bestCandidateErrorState p j winner value reals) =
        bestCandidateAfterError p j winner value a b := @NLA.Proofs.TR04.bestCandidateProgram_error p j winner value reals
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (j winner : ℕ)
    (value a b : ℝ) (hj : j = 0) :
    (ordinaryStep bestCandidateProgram)^[7] (bestCandidateAfterError p j winner value a b) =
      bestCandidateLoopState p (j + 1) j (p.candidateError j)
        (bestCandidateResultScratch p j a b) := @NLA.Proofs.TR04.bestCandidateProgram_first p j winner value a b hj
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (j winner : ℕ)
    (value a b : ℝ) (hj : j ≠ 0) (hlt : p.candidateError j < value) :
    (ordinaryStep bestCandidateProgram)^[7] (bestCandidateAfterError p j winner value a b) =
      bestCandidateLoopState p (j + 1) j (p.candidateError j)
        (bestCandidateResultScratch p j a b) := @NLA.Proofs.TR04.bestCandidateProgram_take p j winner value a b hj hlt
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (j winner : ℕ)
    (value a b : ℝ) (hj : j ≠ 0) (hlt : ¬ p.candidateError j < value) :
    (ordinaryStep bestCandidateProgram)^[7] (bestCandidateAfterError p j winner value a b) =
      bestCandidateLoopState p (j + 1) winner value
        (bestCandidateResultScratch p j a b) := @NLA.Proofs.TR04.bestCandidateProgram_keep p j winner value a b hj hlt
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace) :
    ∃ winner < p.count, ∃ error : ℝ, ∃ result : BestCandidateScratch,
      trace.state (bestCandidateTime p) = bestCandidateFinalState p winner error result ∧
      error = p.candidateError winner ∧ ∀ i < p.count, error ≤ p.candidateError i := @NLA.Proofs.TR04.bestCandidateProgram_trace_result p hp value scratch trace ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace) :
    ∃ winner < p.count,
      (trace.state (bestCandidateTime p)).status = .halted (p.store + winner * p.entries) ∧
      (trace.state (bestCandidateTime p)).natural 5 = winner ∧
      (trace.state (bestCandidateTime p)).natural 6 = p.store + winner * p.entries ∧
      (trace.state (bestCandidateTime p)).real 3 = p.candidateError winner ∧
      (∀ i < p.count, p.candidateError winner ≤ p.candidateError i) ∧
      (trace.state (bestCandidateTime p)).memory = p.memory ∧
      CostThrough bestCandidateProgram trace (bestCandidateTime p) ≤
        50 * (p.count + p.entries + 1)^2 := @NLA.Proofs.TR04.bestCandidateProgram_run p hp value scratch trace ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (p : BestCandidateData) (value : ℝ)
    (scratch : BestCandidateScratch) :
    ∃ trace, LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace := @NLA.Proofs.TR04.bestCandidateProgram_exists_trace p value scratch
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {Q : Program}
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
          (trace.state offset).natural j) := @NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_run_at Q E p hp value scratch start trace ht offset hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {Q : Program}
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
        CostThrough Q trace offset + 50 * (p.count + p.entries + 1)^2 := @NLA.Proofs.TR04.RoutineEmbedding.bestCandidate_value_at Q E p hp value scratch start trace ht offset hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
/-- Empty arrays still produce an actual zero minimum from any initial error. -/
example (p : BestCandidateData) (hp : 0 < p.count) (hN : p.entries = 0)
    (value : ℝ) (scratch : BestCandidateScratch) (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace) :
    ∃ winner < p.count,
      (trace.state (bestCandidateTime p)).status = .halted p.store ∧
      (trace.state (bestCandidateTime p)).real 3 = 0 ∧
      (trace.state (bestCandidateTime p)).memory = p.memory := by
  obtain ⟨winner, hw, hs, _, _, he, _, hm, _⟩ := bestCandidateProgram_run p hp value scratch trace ht
  have hz : p.candidateError winner = 0 := by simp [BestCandidateData.candidateError, squaredErrorSum, hN]
  refine ⟨winner, hw, ?_, he.trans hz, hm⟩
  simpa only [hN, Nat.mul_zero, Nat.add_zero] using hs
end NLA.Proofs.TR04

end
