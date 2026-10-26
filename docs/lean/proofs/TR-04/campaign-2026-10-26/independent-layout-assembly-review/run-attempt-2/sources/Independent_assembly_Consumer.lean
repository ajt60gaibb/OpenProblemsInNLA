import NLA.Proofs.TR04.MachineTTProgramFacts

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
#assert_kind NLA.Proofs.TR04.ttProgram_code_first_svd "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_first_svd
#print axioms NLA.Proofs.TR04.ttProgram_code_first_svd
#assert_kind NLA.Proofs.TR04.ttProgram_code_child_svd "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_child_svd
#print axioms NLA.Proofs.TR04.ttProgram_code_child_svd
#assert_kind NLA.Proofs.TR04.ttProgram_code_header_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_header_exit
#print axioms NLA.Proofs.TR04.ttProgram_code_header_exit
#assert_kind NLA.Proofs.TR04.ttProgram_code_matrix_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_matrix_exit
#print axioms NLA.Proofs.TR04.ttProgram_code_matrix_exit
#assert_kind NLA.Proofs.TR04.ttProgram_code_copy_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_copy_exit
#print axioms NLA.Proofs.TR04.ttProgram_code_copy_exit
#assert_kind NLA.Proofs.TR04.ttProgram_code_gather_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_gather_exit
#print axioms NLA.Proofs.TR04.ttProgram_code_gather_exit
#assert_kind NLA.Proofs.TR04.ttProgram_code_threshold_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_threshold_exit
#print axioms NLA.Proofs.TR04.ttProgram_code_threshold_exit
#assert_kind NLA.Proofs.TR04.ttProgram_code_best_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_best_exit
#print axioms NLA.Proofs.TR04.ttProgram_code_best_exit
#assert_kind NLA.Proofs.TR04.ttProgram_code_caller "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_caller
#print axioms NLA.Proofs.TR04.ttProgram_code_caller
#assert_kind NLA.Proofs.TR04.ttProgram_svd_positions "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_svd_positions
#print axioms NLA.Proofs.TR04.ttProgram_svd_positions
#assert_kind NLA.Proofs.TR04.ttHeader_initial_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttHeader_initial_relates
#print axioms NLA.Proofs.TR04.ttHeader_initial_relates
#assert_kind NLA.Proofs.TR04.ttProgram_trace_exists "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_trace_exists
#print axioms NLA.Proofs.TR04.ttProgram_trace_exists
#assert_kind NLA.Proofs.TR04.ttProgram_header_result "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_header_result
#print axioms NLA.Proofs.TR04.ttProgram_header_result
#assert_kind NLA.Proofs.TR04.ttProgram_header_natural_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.ttProgram_header_natural_outside
#print axioms NLA.Proofs.TR04.ttProgram_header_natural_outside
#assert_kind NLA.Proofs.TR04.ttControllerProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.ttControllerProgram
#print axioms NLA.Proofs.TR04.ttControllerProgram
#assert_kind NLA.Proofs.TR04.ttHeaderRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderRegisters
#print axioms NLA.Proofs.TR04.ttHeaderRegisters
#assert_kind NLA.Proofs.TR04.ttBankStage1 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBankStage1
#print axioms NLA.Proofs.TR04.ttBankStage1
#assert_kind NLA.Proofs.TR04.ttMatrixRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixRegisters
#print axioms NLA.Proofs.TR04.ttMatrixRegisters
#assert_kind NLA.Proofs.TR04.ttBankStage2 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBankStage2
#print axioms NLA.Proofs.TR04.ttBankStage2
#assert_kind NLA.Proofs.TR04.ttCopyRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.ttCopyRegisters
#print axioms NLA.Proofs.TR04.ttCopyRegisters
#assert_kind NLA.Proofs.TR04.ttBankStage3 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBankStage3
#print axioms NLA.Proofs.TR04.ttBankStage3
#assert_kind NLA.Proofs.TR04.ttGatherRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.ttGatherRegisters
#print axioms NLA.Proofs.TR04.ttGatherRegisters
#assert_kind NLA.Proofs.TR04.ttBankStage4 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBankStage4
#print axioms NLA.Proofs.TR04.ttBankStage4
#assert_kind NLA.Proofs.TR04.ttThresholdRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.ttThresholdRegisters
#print axioms NLA.Proofs.TR04.ttThresholdRegisters
#assert_kind NLA.Proofs.TR04.ttBankStage5 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBankStage5
#print axioms NLA.Proofs.TR04.ttBankStage5
#assert_kind NLA.Proofs.TR04.ttBestRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBestRegisters
#print axioms NLA.Proofs.TR04.ttBestRegisters
#assert_kind NLA.Proofs.TR04.ttBankStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBankStage6
#print axioms NLA.Proofs.TR04.ttBankStage6
#assert_kind NLA.Proofs.TR04.ttProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.ttProgram
#print axioms NLA.Proofs.TR04.ttProgram
#assert_kind NLA.Proofs.TR04.ttHeaderEmbeddingStage1 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbeddingStage1
#print axioms NLA.Proofs.TR04.ttHeaderEmbeddingStage1
#assert_kind NLA.Proofs.TR04.ttHeaderEmbeddingStage2 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbeddingStage2
#print axioms NLA.Proofs.TR04.ttHeaderEmbeddingStage2
#assert_kind NLA.Proofs.TR04.ttHeaderEmbeddingStage3 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbeddingStage3
#print axioms NLA.Proofs.TR04.ttHeaderEmbeddingStage3
#assert_kind NLA.Proofs.TR04.ttHeaderEmbeddingStage4 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbeddingStage4
#print axioms NLA.Proofs.TR04.ttHeaderEmbeddingStage4
#assert_kind NLA.Proofs.TR04.ttHeaderEmbeddingStage5 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbeddingStage5
#print axioms NLA.Proofs.TR04.ttHeaderEmbeddingStage5
#assert_kind NLA.Proofs.TR04.ttHeaderEmbeddingStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbeddingStage6
#print axioms NLA.Proofs.TR04.ttHeaderEmbeddingStage6
#assert_kind NLA.Proofs.TR04.ttHeaderEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.ttHeaderEmbedding
#print axioms NLA.Proofs.TR04.ttHeaderEmbedding
#assert_kind NLA.Proofs.TR04.ttMatrixEmbeddingStage2 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixEmbeddingStage2
#print axioms NLA.Proofs.TR04.ttMatrixEmbeddingStage2
#assert_kind NLA.Proofs.TR04.ttMatrixEmbeddingStage3 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixEmbeddingStage3
#print axioms NLA.Proofs.TR04.ttMatrixEmbeddingStage3
#assert_kind NLA.Proofs.TR04.ttMatrixEmbeddingStage4 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixEmbeddingStage4
#print axioms NLA.Proofs.TR04.ttMatrixEmbeddingStage4
#assert_kind NLA.Proofs.TR04.ttMatrixEmbeddingStage5 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixEmbeddingStage5
#print axioms NLA.Proofs.TR04.ttMatrixEmbeddingStage5
#assert_kind NLA.Proofs.TR04.ttMatrixEmbeddingStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixEmbeddingStage6
#print axioms NLA.Proofs.TR04.ttMatrixEmbeddingStage6
#assert_kind NLA.Proofs.TR04.ttMatrixEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.ttMatrixEmbedding
#print axioms NLA.Proofs.TR04.ttMatrixEmbedding
#assert_kind NLA.Proofs.TR04.ttCopyEmbeddingStage3 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttCopyEmbeddingStage3
#print axioms NLA.Proofs.TR04.ttCopyEmbeddingStage3
#assert_kind NLA.Proofs.TR04.ttCopyEmbeddingStage4 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttCopyEmbeddingStage4
#print axioms NLA.Proofs.TR04.ttCopyEmbeddingStage4
#assert_kind NLA.Proofs.TR04.ttCopyEmbeddingStage5 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttCopyEmbeddingStage5
#print axioms NLA.Proofs.TR04.ttCopyEmbeddingStage5
#assert_kind NLA.Proofs.TR04.ttCopyEmbeddingStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttCopyEmbeddingStage6
#print axioms NLA.Proofs.TR04.ttCopyEmbeddingStage6
#assert_kind NLA.Proofs.TR04.ttCopyEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.ttCopyEmbedding
#print axioms NLA.Proofs.TR04.ttCopyEmbedding
#assert_kind NLA.Proofs.TR04.ttGatherEmbeddingStage4 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttGatherEmbeddingStage4
#print axioms NLA.Proofs.TR04.ttGatherEmbeddingStage4
#assert_kind NLA.Proofs.TR04.ttGatherEmbeddingStage5 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttGatherEmbeddingStage5
#print axioms NLA.Proofs.TR04.ttGatherEmbeddingStage5
#assert_kind NLA.Proofs.TR04.ttGatherEmbeddingStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttGatherEmbeddingStage6
#print axioms NLA.Proofs.TR04.ttGatherEmbeddingStage6
#assert_kind NLA.Proofs.TR04.ttGatherEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.ttGatherEmbedding
#print axioms NLA.Proofs.TR04.ttGatherEmbedding
#assert_kind NLA.Proofs.TR04.ttThresholdEmbeddingStage5 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttThresholdEmbeddingStage5
#print axioms NLA.Proofs.TR04.ttThresholdEmbeddingStage5
#assert_kind NLA.Proofs.TR04.ttThresholdEmbeddingStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttThresholdEmbeddingStage6
#print axioms NLA.Proofs.TR04.ttThresholdEmbeddingStage6
#assert_kind NLA.Proofs.TR04.ttThresholdEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.ttThresholdEmbedding
#print axioms NLA.Proofs.TR04.ttThresholdEmbedding
#assert_kind NLA.Proofs.TR04.ttBestEmbeddingStage6 "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBestEmbeddingStage6
#print axioms NLA.Proofs.TR04.ttBestEmbeddingStage6
#assert_kind NLA.Proofs.TR04.ttBestEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.ttBestEmbedding
#print axioms NLA.Proofs.TR04.ttBestEmbedding
#assert_kind NLA.Proofs.TR04.BankRegisters "inductive"
#assert_trust kernel NLA.Proofs.TR04.BankRegisters
#print axioms NLA.Proofs.TR04.BankRegisters
#assert_kind NLA.Proofs.TR04.offsetBankRegisters "definition"
#assert_trust kernel NLA.Proofs.TR04.offsetBankRegisters
#print axioms NLA.Proofs.TR04.offsetBankRegisters
#assert_kind NLA.Proofs.TR04.bankLabel "definition"
#assert_trust kernel NLA.Proofs.TR04.bankLabel
#print axioms NLA.Proofs.TR04.bankLabel
#assert_kind NLA.Proofs.TR04.installCodeBank "definition"
#assert_trust kernel NLA.Proofs.TR04.installCodeBank
#print axioms NLA.Proofs.TR04.installCodeBank
#assert_kind NLA.Proofs.TR04.installCodeBank_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.installCodeBank_outside
#print axioms NLA.Proofs.TR04.installCodeBank_outside
#assert_kind NLA.Proofs.TR04.installedBankEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.installedBankEmbedding
#print axioms NLA.Proofs.TR04.installedBankEmbedding
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.throughInstalledBank "definition"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.throughInstalledBank
#print axioms NLA.Proofs.TR04.RoutineEmbedding.throughInstalledBank
#assert_kind NLA.Proofs.TR04.installCodeBank_exit "theorem"
#assert_trust kernel NLA.Proofs.TR04.installCodeBank_exit
#print axioms NLA.Proofs.TR04.installCodeBank_exit
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
#assert_kind NLA.Proofs.TR04.step_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_total
#print axioms NLA.Proofs.TR04.step_total
#assert_kind NLA.Proofs.TR04.exists_legalTrace "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace
#print axioms NLA.Proofs.TR04.exists_legalTrace
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
#assert_kind NLA.Statements.TR04.Target "definition"
#assert_trust kernel NLA.Statements.TR04.Target
#print axioms NLA.Statements.TR04.Target
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
#assert_kind NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#print axioms NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#assert_kind NLA.Proofs.TR04.SVD.sum_fin_truncate "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_truncate
#print axioms NLA.Proofs.TR04.SVD.sum_fin_truncate
#assert_kind NLA.Proofs.TR04.SVD.exists_validSVD "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_validSVD
#print axioms NLA.Proofs.TR04.SVD.exists_validSVD
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
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside
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
#assert_kind NLA.Proofs.TR04.thresholdScanProgram "definition"
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram
#print axioms NLA.Proofs.TR04.thresholdScanProgram
#assert_kind NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals
#print axioms NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals
#assert_kind NLA.Proofs.TR04.thresholdScanLoopState "definition"
#assert_trust kernel NLA.Proofs.TR04.thresholdScanLoopState
#print axioms NLA.Proofs.TR04.thresholdScanLoopState
#assert_kind NLA.Proofs.TR04.thresholdScanStart "definition"
#assert_trust kernel NLA.Proofs.TR04.thresholdScanStart
#print axioms NLA.Proofs.TR04.thresholdScanStart
#assert_kind NLA.Proofs.TR04.thresholdScanProgram_scalar "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_scalar
#print axioms NLA.Proofs.TR04.thresholdScanProgram_scalar
#assert_kind NLA.Proofs.TR04.thresholdScanProgram_initialize "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_initialize
#print axioms NLA.Proofs.TR04.thresholdScanProgram_initialize
#assert_kind NLA.Proofs.TR04.ThresholdScanParameters "inductive"
#assert_trust kernel NLA.Proofs.TR04.ThresholdScanParameters
#print axioms NLA.Proofs.TR04.ThresholdScanParameters
#assert_kind NLA.Proofs.TR04.thresholdAboveCount "definition"
#assert_trust kernel NLA.Proofs.TR04.thresholdAboveCount
#print axioms NLA.Proofs.TR04.thresholdAboveCount
#assert_kind NLA.Proofs.TR04.thresholdTiedCount "definition"
#assert_trust kernel NLA.Proofs.TR04.thresholdTiedCount
#print axioms NLA.Proofs.TR04.thresholdTiedCount
#assert_kind NLA.Proofs.TR04.thresholdTakeCount "definition"
#assert_trust kernel NLA.Proofs.TR04.thresholdTakeCount
#print axioms NLA.Proofs.TR04.thresholdTakeCount
#assert_kind NLA.Proofs.TR04.thresholdAboveCount_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdAboveCount_zero
#print axioms NLA.Proofs.TR04.thresholdAboveCount_zero
#assert_kind NLA.Proofs.TR04.thresholdTiedCount_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdTiedCount_zero
#print axioms NLA.Proofs.TR04.thresholdTiedCount_zero
#assert_kind NLA.Proofs.TR04.thresholdTakeCount_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdTakeCount_zero
#print axioms NLA.Proofs.TR04.thresholdTakeCount_zero
#assert_kind NLA.Proofs.TR04.thresholdAboveCount_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdAboveCount_succ
#print axioms NLA.Proofs.TR04.thresholdAboveCount_succ
#assert_kind NLA.Proofs.TR04.thresholdTiedCount_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdTiedCount_succ
#print axioms NLA.Proofs.TR04.thresholdTiedCount_succ
#assert_kind NLA.Proofs.TR04.thresholdTakeCount_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.thresholdTakeCount_succ
#print axioms NLA.Proofs.TR04.thresholdTakeCount_succ
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
#assert_kind NLA.Proofs.TR04.headerProductReturnTime "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductReturnTime
#print axioms NLA.Proofs.TR04.headerProductReturnTime
#assert_kind NLA.Proofs.TR04.headerProductReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerProductReturnState
#print axioms NLA.Proofs.TR04.headerProductReturnState
#assert_kind NLA.Proofs.TR04.headerProduct_exit_test "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_exit_test
#print axioms NLA.Proofs.TR04.headerProduct_exit_test
#assert_kind NLA.Proofs.TR04.headerProduct_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_return
#print axioms NLA.Proofs.TR04.headerProduct_return
#assert_kind NLA.Proofs.TR04.headerProduct_return_running "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerProduct_return_running
#print axioms NLA.Proofs.TR04.headerProduct_return_running
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.headerProduct_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.headerProduct_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.headerProduct_run_at
#assert_kind NLA.Proofs.TR04.trace_scalar_block_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.trace_scalar_block_at
#print axioms NLA.Proofs.TR04.trace_scalar_block_at
#assert_kind NLA.Proofs.TR04.trace_svd_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.trace_svd_at
#print axioms NLA.Proofs.TR04.trace_svd_at

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (P Q : Program) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1)
    (label : Fin (Q.extraLabels+1))
    (outside : ¬(base≤label.val ∧ label.val<base+(P.extraLabels+1))) :
    (installCodeBank P Q registers base fits).code label = Q.code label := @NLA.Proofs.TR04.installCodeBank_outside P Q registers base fits label outside
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (P Q : Program) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1)
    (label : Fin (P.extraLabels+1)) (halt : instructionIsHalt (P.code label)=true) :
    (installCodeBank P Q registers base fits).code (bankLabel P Q base fits label) =
      Q.code (bankLabel P Q base fits label) := @NLA.Proofs.TR04.installCodeBank_exit P Q registers base fits label halt
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {P : Program} {start : State P} {trace : Trace P}
    (ht : LegalTrace P start trace) (offset n : ℕ)
    (hscalar : ∀ k<n,((ordinaryStep P)^[k] (trace.state offset)).status=.running →
      instructionIsSVD (P.code ((ordinaryStep P)^[k] (trace.state offset)).label)=false) :
    trace.state (offset+n)=(ordinaryStep P)^[n] (trace.state offset) ∧
    CostThrough P trace (offset+n)≤CostThrough P trace offset+n := @NLA.Proofs.TR04.trace_scalar_block_at P start trace ht offset n hscalar
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {P : Program} {start : State P} {trace : Trace P}
    (ht : LegalTrace P start trace) (time : ℕ)
    (rows cols inputBase uBase sigmaBase vBase : Fin (P.extraNatRegisters+1))
    (next : Fin (P.extraLabels+1))
    (hcode : P.code (trace.state time).label=.svd rows cols inputBase uBase sigmaBase vBase next)
    (hs : (trace.state time).status=.running)
    (hd : OutputBlocksDisjoint ((trace.state time).natural rows) ((trace.state time).natural cols)
      ((trace.state time).natural uBase) ((trace.state time).natural sigmaBase) ((trace.state time).natural vBase)) :
    ∃ U : Matrix (Fin ((trace.state time).natural rows)) (Fin ((trace.state time).natural rows)) ℝ,
    ∃ sigma : Fin (min ((trace.state time).natural rows) ((trace.state time).natural cols)) → ℝ,
    ∃ V : Matrix (Fin ((trace.state time).natural cols)) (Fin ((trace.state time).natural cols)) ℝ,
      ValidSVD (readMatrix (trace.state time).memory ((trace.state time).natural rows)
        ((trace.state time).natural cols) ((trace.state time).natural inputBase)) U sigma V ∧
      trace.state (time+1) =
        { (trace.state time) with
          label := next
          memory := writeSVD (trace.state time).memory ((trace.state time).natural uBase)
            ((trace.state time).natural sigmaBase) ((trace.state time).natural vBase) U sigma V } ∧
      trace.cost time=(((trace.state time).natural rows)+((trace.state time).natural cols)+1)^3 := @NLA.Proofs.TR04.trace_svd_at P start trace ht time rows cols inputBase uBase sigmaBase vBase next hcode hs hd
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 167 = .svd 81 82 92 72 73 74 168 := @NLA.Proofs.TR04.ttProgram_code_first_svd 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 237 = .svd 85 87 89 94 103 104 238 := @NLA.Proofs.TR04.ttProgram_code_child_svd 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 10 = .jump 372 := @NLA.Proofs.TR04.ttProgram_code_header_exit 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 32 = .equalNat 97 127 274 394 := @NLA.Proofs.TR04.ttProgram_code_matrix_exit 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 39 = .jump 355 := @NLA.Proofs.TR04.ttProgram_code_copy_exit 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 65 = .jump 198 := @NLA.Proofs.TR04.ttProgram_code_gather_exit 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 88 = .jump 179 := @NLA.Proofs.TR04.ttProgram_code_threshold_exit 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ttProgram.code 114 = .copyNat 83 55 371 := @NLA.Proofs.TR04.ttProgram_code_best_exit 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (label : Fin 512) (hl : 119≤label.val) :
    ttProgram.code label=ttControllerProgram.code label := @NLA.Proofs.TR04.ttProgram_code_caller label hl
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : ∀ label : Fin 512,
    instructionIsSVD (ttProgram.code label) = true ↔ label.val=167 ∨ label.val=237 := @NLA.Proofs.TR04.ttProgram_svd_positions 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (memory : ℕ → ℝ) (d : ℕ) :
    ttHeaderEmbedding.Relates (initial headerProductProgram d memory) (initial ttProgram d memory) := @NLA.Proofs.TR04.ttHeader_initial_relates memory d
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ trace : Trace ttProgram,LegalTrace ttProgram (Start ttProgram S r A) trace := @NLA.Proofs.TR04.ttProgram_trace_exists S r A
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).label=10 ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).status=.running ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).natural 2=DenseSize S ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).memory=InputMemory S r A ∧
    CostThrough ttProgram trace (headerProductReturnTime (shapeHeaderValues S) S.order)≤7*Size S r := @NLA.Proofs.TR04.ttProgram_header_result S r A trace ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace)
    (j : Fin 128) (hj : 4≤j.val) :
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).natural j=0 := @NLA.Proofs.TR04.ttProgram_header_natural_outside S r A trace ht j hj
end NLA.Proofs.TR04

namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

example : ttProgram.extraLabels = 511 ∧ ttProgram.realRegisters = 16 ∧
    ttProgram.extraNatRegisters = 127 ∧ ttProgram.constantCount = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- These are genuine embeddings into the complete fixed caller, with actual code fields.
example : RoutineEmbedding headerProductProgram ttProgram := ttHeaderEmbedding
example : RoutineEmbedding matrixMultiplyProgram ttProgram := ttMatrixEmbedding
example : RoutineEmbedding copyProgram ttProgram := ttCopyEmbedding
example : RoutineEmbedding frameGatherProgram ttProgram := ttGatherEmbedding
example : RoutineEmbedding thresholdScanProgram ttProgram := ttThresholdEmbedding
example : RoutineEmbedding bestCandidateProgram ttProgram := ttBestEmbedding

-- The corrected prefix fallback provides the actual positive tied count to its callee.
example : ttProgram.code 185 = .natural 78 1 186 := rfl

example (S : Shape) (r : Ranks S) (A : Tensor S) (trace : Trace ttProgram)
    (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).natural 97 = 0 ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).natural 127 = 0 :=
  ⟨ttProgram_header_natural_outside S r A trace ht 97 (by decide),
   ttProgram_header_natural_outside S r A trace ht 127 (by decide)⟩

-- Every legal reply at the first literal SVD site retains the full actual tuple,
-- memory write and cubic charge. No favorable reply is selected.
example (start : State ttProgram) (trace : Trace ttProgram)
    (ht : LegalTrace ttProgram start trace) (time : ℕ)
    (hl : (trace.state time).label = 167) (hs : (trace.state time).status = .running)
    (hd : OutputBlocksDisjoint ((trace.state time).natural 81) ((trace.state time).natural 82)
      ((trace.state time).natural 72) ((trace.state time).natural 73) ((trace.state time).natural 74)) :
    ∃ U : Matrix (Fin ((trace.state time).natural 81)) (Fin ((trace.state time).natural 81)) ℝ,
    ∃ sigma : Fin (min ((trace.state time).natural 81) ((trace.state time).natural 82)) → ℝ,
    ∃ V : Matrix (Fin ((trace.state time).natural 82)) (Fin ((trace.state time).natural 82)) ℝ,
      ValidSVD (readMatrix (trace.state time).memory ((trace.state time).natural 81)
        ((trace.state time).natural 82) ((trace.state time).natural 92)) U sigma V ∧
      trace.state (time + 1) =
        { (trace.state time) with
          label := 168
          memory := writeSVD (trace.state time).memory ((trace.state time).natural 72)
            ((trace.state time).natural 73) ((trace.state time).natural 74) U sigma V } ∧
      trace.cost time = (((trace.state time).natural 81) + ((trace.state time).natural 82) + 1)^3 := by
  have hc : ttProgram.code (trace.state time).label = .svd 81 82 92 72 73 74 168 := by
    rw [hl]
    exact ttProgram_code_first_svd
  exact trace_svd_at ht time 81 82 92 72 73 74 168 hc hs hd

-- The separate child site has its own actual row/column/input/output registers.
example (start : State ttProgram) (trace : Trace ttProgram)
    (ht : LegalTrace ttProgram start trace) (time : ℕ)
    (hl : (trace.state time).label = 237) (hs : (trace.state time).status = .running)
    (hd : OutputBlocksDisjoint ((trace.state time).natural 85) ((trace.state time).natural 87)
      ((trace.state time).natural 94) ((trace.state time).natural 103) ((trace.state time).natural 104)) :
    ∃ U : Matrix (Fin ((trace.state time).natural 85)) (Fin ((trace.state time).natural 85)) ℝ,
    ∃ sigma : Fin (min ((trace.state time).natural 85) ((trace.state time).natural 87)) → ℝ,
    ∃ V : Matrix (Fin ((trace.state time).natural 87)) (Fin ((trace.state time).natural 87)) ℝ,
      ValidSVD (readMatrix (trace.state time).memory ((trace.state time).natural 85)
        ((trace.state time).natural 87) ((trace.state time).natural 89)) U sigma V ∧
      trace.state (time + 1) =
        { (trace.state time) with
          label := 238
          memory := writeSVD (trace.state time).memory ((trace.state time).natural 94)
            ((trace.state time).natural 103) ((trace.state time).natural 104) U sigma V } ∧
      trace.cost time = (((trace.state time).natural 85) + ((trace.state time).natural 87) + 1)^3 := by
  have hc : ttProgram.code (trace.state time).label = .svd 85 87 89 94 103 104 238 := by
    rw [hl]
    exact ttProgram_code_child_svd
  exact trace_svd_at ht time 85 87 89 94 103 104 238 hc hs hd

end NLA.Proofs.TR04

end
