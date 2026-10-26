import NLA.Proofs.TR04.MachineHeaderProductRange

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
#assert_kind NLA.Proofs.TR04.headerRangeValues "definition"
#assert_trust kernel NLA.Proofs.TR04.headerRangeValues
#print axioms NLA.Proofs.TR04.headerRangeValues
#assert_kind NLA.Proofs.TR04.headerRangeProduct "definition"
#assert_trust kernel NLA.Proofs.TR04.headerRangeProduct
#print axioms NLA.Proofs.TR04.headerRangeProduct
#assert_kind NLA.Proofs.TR04.headerRangeTime "definition"
#assert_trust kernel NLA.Proofs.TR04.headerRangeTime
#print axioms NLA.Proofs.TR04.headerRangeTime
#assert_kind NLA.Proofs.TR04.headerRange_prefix_start "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_prefix_start
#print axioms NLA.Proofs.TR04.headerRange_prefix_start
#assert_kind NLA.Proofs.TR04.headerRange_prefix_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_prefix_product
#print axioms NLA.Proofs.TR04.headerRange_prefix_product
#assert_kind NLA.Proofs.TR04.headerRange_iterations "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_iterations
#print axioms NLA.Proofs.TR04.headerRange_iterations
#assert_kind NLA.Proofs.TR04.headerRangeEntryState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerRangeEntryState
#print axioms NLA.Proofs.TR04.headerRangeEntryState
#assert_kind NLA.Proofs.TR04.headerRangeReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerRangeReturnState
#print axioms NLA.Proofs.TR04.headerRangeReturnState
#assert_kind NLA.Proofs.TR04.headerRange_entry_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_entry_product
#print axioms NLA.Proofs.TR04.headerRange_entry_product
#assert_kind NLA.Proofs.TR04.headerRange_entry_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_entry_eq
#print axioms NLA.Proofs.TR04.headerRange_entry_eq
#assert_kind NLA.Proofs.TR04.headerRange_return_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_return_product
#print axioms NLA.Proofs.TR04.headerRange_return_product
#assert_kind NLA.Proofs.TR04.headerRange_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_return
#print axioms NLA.Proofs.TR04.headerRange_return
#assert_kind NLA.Proofs.TR04.headerRange_time_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerRange_time_le
#print axioms NLA.Proofs.TR04.headerRange_time_le
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.headerRange_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.headerRange_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.headerRange_run_at
#assert_kind NLA.Proofs.TR04.headerSingleReturnState "definition"
#assert_trust kernel NLA.Proofs.TR04.headerSingleReturnState
#print axioms NLA.Proofs.TR04.headerSingleReturnState
#assert_kind NLA.Proofs.TR04.headerSingle_after_decode "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerSingle_after_decode
#print axioms NLA.Proofs.TR04.headerSingle_after_decode
#assert_kind NLA.Proofs.TR04.headerSingle_return "theorem"
#assert_trust kernel NLA.Proofs.TR04.headerSingle_return
#print axioms NLA.Proofs.TR04.headerSingle_return
#assert_kind NLA.Proofs.TR04.RoutineEmbedding.headerSingle_run_at "theorem"
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.headerSingle_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.headerSingle_run_at
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

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (d value : ℕ) :
    (ordinaryStep headerProductProgram)^[3] (headerProductAfterDecode memory d d 1 value) =
      headerSingleReturnState memory d value := @NLA.Proofs.TR04.headerSingle_after_decode memory d value
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (d value : ℕ) (scratch : ℝ) :
    (ordinaryStep headerProductProgram)^[3*value+5]
      (headerProductDecodeState memory d d 1 value scratch) = headerSingleReturnState memory d value := @NLA.Proofs.TR04.headerSingle_return memory d value scratch
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {Q : Program}
    (E : RoutineEmbedding headerProductProgram Q) (memory : ℕ → ℝ) (d value : ℕ) (scratch : ℝ)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (headerProductDecodeState memory d d 1 value scratch) (trace.state offset)) :
    E.Relates (headerSingleReturnState memory d value) (trace.state (offset+(3*value+5))) ∧
      CostThrough Q trace (offset+(3*value+5)) ≤ CostThrough Q trace offset+(3*value+5) := @NLA.Proofs.TR04.RoutineEmbedding.headerSingle_run_at Q E memory d value scratch start trace ht offset hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (values : ℕ → ℕ) (a : ℕ) :
    headerPrefixProduct (headerRangeValues values a) a = 1 := @NLA.Proofs.TR04.headerRange_prefix_start values a
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (values : ℕ → ℕ) (a d : ℕ) (had : a≤d) :
    headerPrefixProduct (headerRangeValues values a) d = headerRangeProduct values a d := @NLA.Proofs.TR04.headerRange_prefix_product values a d had
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    headerRangeEntryState memory d a values counter reals =
      { label := 2,real := reals,natural := ![d,a,1,counter],
        memory := memory,status := .running } := @NLA.Proofs.TR04.headerRange_entry_eq memory d a values counter reals
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) (had : a≤d) :
    (headerRangeReturnState memory d a values counter reals).natural 2 =
      headerRangeProduct values a d := @NLA.Proofs.TR04.headerRange_return_product memory d a values counter reals had
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ) (had : a≤d)
    (hm : ∀ j, a≤j → j<d → memory j = (values j : ℝ))
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    ∃ last : ℕ, ∃ registers : Fin 2 → ℝ,
      (ordinaryStep headerProductProgram)^[headerRangeTime values a d]
        (headerRangeEntryState memory d a values counter reals) =
          headerRangeReturnState memory d a values last registers := @NLA.Proofs.TR04.headerRange_return memory d a values had hm counter reals
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (values : ℕ → ℕ) (a d : ℕ) :
    headerRangeTime values a d ≤ headerPrefixTime values d+1 := @NLA.Proofs.TR04.headerRange_time_le values a d
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {Q : Program}
    (E : RoutineEmbedding headerProductProgram Q) (memory : ℕ → ℝ)
    (d a : ℕ) (values : ℕ → ℕ) (had : a≤d)
    (hm : ∀ j, a≤j → j<d → memory j = (values j : ℝ))
    (counter : ℕ) (reals : Fin 2 → ℝ) {start : State Q} {trace : Trace Q}
    (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (headerRangeEntryState memory d a values counter reals) (trace.state offset)) :
    ∃ last : ℕ, ∃ registers : Fin 2 → ℝ,
      E.Relates (headerRangeReturnState memory d a values last registers)
        (trace.state (offset+headerRangeTime values a d)) ∧
      CostThrough Q trace (offset+headerRangeTime values a d) ≤
        CostThrough Q trace offset+headerRangeTime values a d := @NLA.Proofs.TR04.RoutineEmbedding.headerRange_run_at Q E memory d a values had hm counter reals start trace ht offset hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
/-- Actual caller fields after the single-value decoder entry. -/
example {Q : Program} (E : RoutineEmbedding headerProductProgram Q)
    (memory : ℕ → ℝ) (d value : ℕ) (scratch : ℝ)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (headerProductDecodeState memory d d 1 value scratch) (trace.state offset)) :
    (trace.state (offset + (3 * value + 5))).natural (E.naturals 2) = value ∧
      (trace.state (offset + (3 * value + 5))).memory = memory ∧
      (trace.state (offset + (3 * value + 5))).status = .running ∧
      CostThrough Q trace (offset + (3 * value + 5)) ≤
        CostThrough Q trace offset + (3 * value + 5) := by
  obtain ⟨hr, hc⟩ := E.headerSingle_run_at memory d value scratch ht offset hs
  exact ⟨hr.natural_apply 2, hr.memory, hr.status, hc⟩

/-- Actual caller fields expose the suffix product with no prefix-cell premise. -/
example {Q : Program} (E : RoutineEmbedding headerProductProgram Q)
    (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ) (had : a ≤ d)
    (hm : ∀ j, a ≤ j → j < d → memory j = (values j : ℝ))
    (counter : ℕ) (reals : Fin 2 → ℝ)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (headerRangeEntryState memory d a values counter reals) (trace.state offset)) :
    (trace.state (offset + headerRangeTime values a d)).natural (E.naturals 2) =
        headerRangeProduct values a d ∧
      (trace.state (offset + headerRangeTime values a d)).memory = memory ∧
      (trace.state (offset + headerRangeTime values a d)).status = .running ∧
      CostThrough Q trace (offset + headerRangeTime values a d) ≤
        CostThrough Q trace offset + headerRangeTime values a d := by
  obtain ⟨last, registers, hr, hc⟩ := E.headerRange_run_at memory d a values had hm
    counter reals ht offset hs
  exact ⟨(hr.natural_apply 2).trans (headerRange_return_product memory d a values last registers had),
    hr.memory, hr.status, hc⟩
end NLA.Proofs.TR04

end
