import NLA.Proofs.TR04.MachineTTForward

set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#audit_named " user:str modName:str visibility:str expected:str : command => do
  unless visibility.getString == "public" || visibility.getString == "private" || visibility.getString == "local" do
    throwErrorAt visibility "unsupported visibility"
  let decl := if visibility.getString == "private" then
    Lean.mkPrivateNameCore modName.getString.toName user.getString.toName
    else user.getString.toName
  let some info := (← getEnv).find? decl | throwErrorAt user "missing exact compiler constant {decl}"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt user "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {user.getString} {expected.getString}"
  logInfo m!"AUDITED_ACTUAL {user.getString} {decl.toString} {visibility.getString}"
  elabCommand (← `(#assert_trust $(mkIdent `kernel) $(mkIdent decl)))
  elabCommand (← `(#print axioms $(mkIdent decl)))
  let axs ← liftCoreM <| collectAxioms decl
  let body := String.intercalate "," (axs.toList.map Name.toString)
  logInfo m!"AUDITED_AXIOMS {user.getString} [{body}]"
#audit_named "NLA.Computation.SVDMachine.Instruction" "NLA.Computation.SVDMachine" "public" "inductive"
#audit_named "NLA.Computation.SVDMachine.Program" "NLA.Computation.SVDMachine" "public" "inductive"
#audit_named "NLA.Computation.SVDMachine.Status" "NLA.Computation.SVDMachine" "public" "inductive"
#audit_named "NLA.Computation.SVDMachine.State" "NLA.Computation.SVDMachine" "public" "inductive"
#audit_named "NLA.Computation.SVDMachine.initial" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.ordinaryStep" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.ValidSVD" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.DisjointBlocks" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.OutputBlocksDisjoint" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.matrixCell" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.readMatrix" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.writeSVD" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.charge" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.Step" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.Trace" "NLA.Computation.SVDMachine" "public" "inductive"
#audit_named "NLA.Computation.SVDMachine.LegalTrace" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.SVDMachine.CostThrough" "NLA.Computation.SVDMachine" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Shape" "NLA.Computation.TensorTrainApproximation" "public" "inductive"
#audit_named "NLA.Computation.TensorTrainApproximation.Index" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Tensor" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Cut" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Ranks" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.RowIndex" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.ColIndex" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.join" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Unfold" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Feasible" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.FrobeniusSq" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Optimum" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.DenseSize" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.SuffixSize" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Offset" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Decode" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.InputMemory" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Start" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Returns" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Computation.TensorTrainApproximation.Size" "NLA.Computation.TensorTrainApproximation" "public" "definition"
#audit_named "NLA.Statements.TR04.Target" "NLA.Statements.TR04" "public" "definition"
#audit_named "NLA.Proofs.TR04.step_cost_eq" "NLA.Proofs.TR04.MachineExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.step_of_halted" "NLA.Proofs.TR04.MachineExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.step_of_failed" "NLA.Proofs.TR04.MachineExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.exists_legalTrace_of_step_total" "NLA.Proofs.TR04.MachineExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.step_total_of_svd_total" "NLA.Proofs.TR04.MachineExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.exists_legalTrace_of_svd_total" "NLA.Proofs.TR04.MachineExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.Space" "NLA.Proofs.TR04.SVDCore" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.rightBasis" "NLA.Proofs.TR04.SVDCore" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.norm_image_rightBasis" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.inner_image_rightBasis" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.range_finrank_le_domain" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.range_finrank_le_codomain" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.leftVector" "NLA.Proofs.TR04.SVDCore" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.exists_leftBasis" "NLA.Proofs.TR04.SVDCore" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul" "NLA.Proofs.TR04.SVDTotal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_fin_truncate" "NLA.Proofs.TR04.SVDTotal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.exists_validSVD" "NLA.Proofs.TR04.SVDTotal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.step_total" "NLA.Proofs.TR04.MachineTotality" "public" "theorem"
#audit_named "NLA.Proofs.TR04.exists_legalTrace" "NLA.Proofs.TR04.MachineTotality" "public" "theorem"
#audit_named "NLA.Proofs.TR04.legalTrace_cost_eq" "NLA.Proofs.TR04.MachineTraceBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_zero" "NLA.Proofs.TR04.MachineTraceBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_succ" "NLA.Proofs.TR04.MachineTraceBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.charge_pos_of_running" "NLA.Proofs.TR04.MachineTraceBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.legalTrace_halted_state_add" "NLA.Proofs.TR04.MachineTraceBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_add_of_halted" "NLA.Proofs.TR04.MachineTraceBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.machineState_ext" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.instructionIsSVD" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "definition"
#audit_named "NLA.Proofs.TR04.step_iff_ordinary_of_scalar" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.legalTrace_scalar_prefix" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_scalar_prefix" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.charge_le_one_of_scalar" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_le_scalar" "NLA.Proofs.TR04.MachineScalarBlocks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.instructionIsHalt" "NLA.Proofs.TR04.MachineRelocation" "public" "definition"
#audit_named "NLA.Proofs.TR04.relocateInstruction" "NLA.Proofs.TR04.MachineRelocation" "public" "definition"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding" "NLA.Proofs.TR04.MachineRelocation" "public" "inductive"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.Relates" "NLA.Proofs.TR04.MachineRelocation" "public" "inductive"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.Relates.real_apply" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.Relates.natural_apply" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_relates" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.instructionIsSVD_relocate" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.charge_eq" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.scalar_step" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_prefix" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost_le" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_real_outside" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_natural_outside" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_real_outside" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_natural_outside" "NLA.Proofs.TR04.MachineRelocation" "public" "theorem"
#audit_named "NLA.Proofs.TR04.BankRegisters" "NLA.Proofs.TR04.MachineCodeBanks" "public" "inductive"
#audit_named "NLA.Proofs.TR04.offsetBankRegisters" "NLA.Proofs.TR04.MachineCodeBanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.bankLabel" "NLA.Proofs.TR04.MachineCodeBanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.installCodeBank" "NLA.Proofs.TR04.MachineCodeBanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.installCodeBank_outside" "NLA.Proofs.TR04.MachineCodeBanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.installedBankEmbedding" "NLA.Proofs.TR04.MachineCodeBanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.throughInstalledBank" "NLA.Proofs.TR04.MachineCodeBanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.installCodeBank_exit" "NLA.Proofs.TR04.MachineCodeBanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_relates" "NLA.Proofs.TR04.MachineRelocationOrdinary" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_natural_outside" "NLA.Proofs.TR04.MachineRelocationOrdinary" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.ordinary_iterate_real_outside" "NLA.Proofs.TR04.MachineRelocationOrdinary" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram" "NLA.Proofs.TR04.MachineCopy" "public" "definition"
#audit_named "NLA.Proofs.TR04.copiedMemory" "NLA.Proofs.TR04.MachineCopy" "public" "definition"
#audit_named "NLA.Proofs.TR04.copyLoopState" "NLA.Proofs.TR04.MachineCopy" "public" "definition"
#audit_named "NLA.Proofs.TR04.copiedMemory_zero" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copiedMemory_outside" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copiedMemory_source_next" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copiedMemory_succ" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_scalar" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_six_steps" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_iterations" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyFinalState" "NLA.Proofs.TR04.MachineCopy" "public" "definition"
#audit_named "NLA.Proofs.TR04.copyProgram_exit" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_trace_result" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_trace_cells" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_trace_cost" "NLA.Proofs.TR04.MachineCopy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "definition"
#audit_named "NLA.Proofs.TR04.decodeNaturalLoopState" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "definition"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_scalar" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_three_steps" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_iterations" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalFinalState" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "definition"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_exit" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_trace_result" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_trace_cost" "NLA.Proofs.TR04.MachineHeaderDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_nohalt_phase" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyProgram_nohalt_prefix" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.copyReturnState" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "definition"
#audit_named "NLA.Proofs.TR04.copyProgram_return" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.copy_run" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_nohalt_phase" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_nohalt_initial" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_nohalt_prefix" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.decodeNaturalReturnState" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "definition"
#audit_named "NLA.Proofs.TR04.decodeNaturalProgram_return" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run" "NLA.Proofs.TR04.MachineScalarRoutines" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductProgram" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerDecoderLabelMap" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerDecoderNatMap" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerDecoderEmbedding" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerPrefixProduct" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerPrefixTime" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProductLoopState" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProductDecodeState" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProductProgram_scalar" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_setup" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_decode_relates" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductAfterDecode" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProduct_decode" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerPrefixProduct_succ" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerPrefixTime_succ" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_finish" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_iteration" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_iterations" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_initial" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductFinalState" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProduct_exit" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductTime" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProduct_trace_result" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_trace_cost" "NLA.Proofs.TR04.MachineHeaderProduct" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrix_offset_lt" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixCell_entry" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.disjointBlocks_not_mem_right" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.disjointBlocks_not_mem_left" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.writeSVD_u_entry" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.readMatrix_writeSVD_u" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.writeSVD_sigma_entry" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.writeSVD_v_entry" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.readMatrix_writeSVD_v" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.writeSVD_outside" "NLA.Proofs.TR04.MachineSVDMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "inductive"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.bAddress" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.cAddress" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.productMatrix" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_transpose" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.partialProduct" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_zero" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.partialProduct_succ" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.productMatrix_entry" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.InputsOutsideOutput" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.prefixMemory" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.prefixMemory_zero" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.prefixMemory_outside" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.prefixMemory_update" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_source" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_b" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_c" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_update" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.outputPrefix_read" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput" "NLA.Proofs.TR04.MachineMatrixMultiplyMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "definition"
#audit_named "NLA.Proofs.TR04.MatrixMultiplyScratch" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "inductive"
#audit_named "NLA.Proofs.TR04.matrixMultiplyState" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyCellState" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyInnerState" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyRowState" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_scalar" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_cell_setup" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_inner_eight" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_inner_iterations" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_cell_exit" "NLA.Proofs.TR04.MachineMatrixMultiply" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shiftedTrace" "NLA.Proofs.TR04.MachineTraceComposition" "public" "definition"
#audit_named "NLA.Proofs.TR04.legalTrace_shift" "NLA.Proofs.TR04.MachineTraceComposition" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_shift" "NLA.Proofs.TR04.MachineTraceComposition" "public" "theorem"
#audit_named "NLA.Proofs.TR04.costThrough_compose_le" "NLA.Proofs.TR04.MachineTraceComposition" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.copy_run_at" "NLA.Proofs.TR04.MachineTraceComposition" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run_at" "NLA.Proofs.TR04.MachineTraceComposition" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "inductive"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.width" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.Valid" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "inductive"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.counter" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.column" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.sourceAddress" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.counter_prefix" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.counter_lt" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.counter_succ" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.column_lt" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_mem" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMemory" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_zero" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_outside" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_succ" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_input" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_read" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_output" "NLA.Proofs.TR04.MachineFrameGatherMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ordinaryStep_eq_of_stopped" "NLA.Proofs.TR04.MachineNoEarlyHalt" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ordinary_iterate_eq_of_stopped" "NLA.Proofs.TR04.MachineNoEarlyHalt" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ordinary_running_prefix" "NLA.Proofs.TR04.MachineNoEarlyHalt" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ordinary_nohalt_prefix_of_running" "NLA.Proofs.TR04.MachineNoEarlyHalt" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram" "NLA.Proofs.TR04.MachineFrameGather" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherOuterState" "NLA.Proofs.TR04.MachineFrameGather" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherStart" "NLA.Proofs.TR04.MachineFrameGather" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherInnerState" "NLA.Proofs.TR04.MachineFrameGather" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_scalar" "NLA.Proofs.TR04.MachineFrameGather" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_initialize" "NLA.Proofs.TR04.MachineFrameGather" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_row_setup" "NLA.Proofs.TR04.MachineFrameGather" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ThresholdScanParameters" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "inductive"
#audit_named "NLA.Proofs.TR04.thresholdAboveCount" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdTiedCount" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdTakeCount" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdAboveCount_zero" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdTiedCount_zero" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdTakeCount_zero" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdAboveCount_succ" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdTiedCount_succ" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdTakeCount_succ" "NLA.Proofs.TR04.MachineThresholdScanCounts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram" "NLA.Proofs.TR04.MachineThresholdScan" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals" "NLA.Proofs.TR04.MachineThresholdScan" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdScanLoopState" "NLA.Proofs.TR04.MachineThresholdScan" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdScanStart" "NLA.Proofs.TR04.MachineThresholdScan" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_scalar" "NLA.Proofs.TR04.MachineThresholdScan" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_initialize" "NLA.Proofs.TR04.MachineThresholdScan" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram" "NLA.Proofs.TR04.MachineSquaredError" "public" "definition"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorSum" "NLA.Proofs.TR04.MachineSquaredError" "public" "definition"
#audit_named "NLA.Proofs.TR04.squaredErrorSum_zero" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorSum_succ" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorLoopState" "NLA.Proofs.TR04.MachineSquaredError" "public" "definition"
#audit_named "NLA.Proofs.TR04.squaredErrorStart" "NLA.Proofs.TR04.MachineSquaredError" "public" "definition"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_scalar" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_initialize" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_nine_steps" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_iterations" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorFinalState" "NLA.Proofs.TR04.MachineSquaredError" "public" "definition"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_exit" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_finish" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_trace_result" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_trace_cost" "NLA.Proofs.TR04.MachineSquaredError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_nohalt_phase" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_nohalt_loop_prefix" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_nohalt_prefix" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.squaredErrorReturnState" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.squaredErrorProgram_return" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.squaredError_run" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_at" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.squaredError_run_value" "NLA.Proofs.TR04.MachineSquaredErrorTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.BestCandidateData" "NLA.Proofs.TR04.MachineBestCandidateMemory" "public" "inductive"
#audit_named "NLA.Proofs.TR04.BestCandidateData.candidateBase" "NLA.Proofs.TR04.MachineBestCandidateMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.BestCandidateData.candidateError" "NLA.Proofs.TR04.MachineBestCandidateMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.BestCandidateData.MinimumSoFar" "NLA.Proofs.TR04.MachineBestCandidateMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.BestCandidateData.minimum_take" "NLA.Proofs.TR04.MachineBestCandidateMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.BestCandidateData.minimum_keep" "NLA.Proofs.TR04.MachineBestCandidateMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.bestCandidateProgram" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters" "NLA.Proofs.TR04.MachineBestCandidate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.bestCandidateErrorLabels" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateErrorNaturals" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateErrorReals" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateErrorEmbedding" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.BestCandidateScratch" "NLA.Proofs.TR04.MachineBestCandidate" "public" "inductive"
#audit_named "NLA.Proofs.TR04.bestCandidateState" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateLoopState" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateErrorState" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateAfterError" "NLA.Proofs.TR04.MachineBestCandidate" "public" "definition"
#audit_named "NLA.Proofs.TR04.bestCandidateProgram_scalar" "NLA.Proofs.TR04.MachineBestCandidate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.bestCandidateProgram_setup" "NLA.Proofs.TR04.MachineBestCandidate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.bestCandidate_error_relates" "NLA.Proofs.TR04.MachineBestCandidate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttControllerProgram" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderRegisters" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBankStage1" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixRegisters" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBankStage2" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttCopyRegisters" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBankStage3" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttGatherRegisters" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBankStage4" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttThresholdRegisters" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBankStage5" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBestRegisters" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBankStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttProgram" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbeddingStage1" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbeddingStage2" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbeddingStage3" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbeddingStage4" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbeddingStage5" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbeddingStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderEmbedding" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixEmbeddingStage2" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixEmbeddingStage3" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixEmbeddingStage4" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixEmbeddingStage5" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixEmbeddingStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMatrixEmbedding" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttCopyEmbeddingStage3" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttCopyEmbeddingStage4" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttCopyEmbeddingStage5" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttCopyEmbeddingStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttCopyEmbedding" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttGatherEmbeddingStage4" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttGatherEmbeddingStage5" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttGatherEmbeddingStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttGatherEmbedding" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttThresholdEmbeddingStage5" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttThresholdEmbeddingStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttThresholdEmbedding" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBestEmbeddingStage6" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttBestEmbedding" "NLA.Proofs.TR04.MachineTTProgram" "public" "definition"
#audit_named "NLA.Proofs.TR04.shapeHeaderValues" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "definition"
#audit_named "NLA.Proofs.TR04.shapeHeaderValues_fin" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.inputMemory_shapeHeader" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shapeHeaderValues_sum" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shapeHeaderValues_product" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.fin_sum_le_prod_of_two_le_aux" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.fin_sum_le_prod_of_two_le" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_sum_modes_le_denseSize" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_denseSize_pos" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_order_le_denseSize" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_mode_le_denseSize" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_suffix_pos" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_suffix_le_denseSize" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_denseSize_le_size" "NLA.Proofs.TR04.ShapeInitializationBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerPrefixProduct_shape" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerPrefixProduct_shape_le" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerPrefixTime_shape" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductTime_shape" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductTime_shape_le_size" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_headerProduct_trace_exists" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.shape_headerProduct_trace_result" "NLA.Proofs.TR04.MachineHeaderProductOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProductReturnTime" "NLA.Proofs.TR04.MachineHeaderProductCallable" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProductReturnState" "NLA.Proofs.TR04.MachineHeaderProductCallable" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerProduct_exit_test" "NLA.Proofs.TR04.MachineHeaderProductCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_return" "NLA.Proofs.TR04.MachineHeaderProductCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerProduct_return_running" "NLA.Proofs.TR04.MachineHeaderProductCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.headerProduct_run_at" "NLA.Proofs.TR04.MachineHeaderProductCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.trace_scalar_block_at" "NLA.Proofs.TR04.MachineInstructionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.trace_svd_at" "NLA.Proofs.TR04.MachineInstructionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_first_svd" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_child_svd" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_header_exit" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_matrix_exit" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_copy_exit" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_gather_exit" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_threshold_exit" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_best_exit" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_caller" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_svd_positions" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeader_initial_relates" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_trace_exists" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_header_result" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_header_natural_outside" "NLA.Proofs.TR04.MachineTTProgramFacts" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderHandler" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderTagLabel" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderCompareLabel" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderRejectLabel" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttProgram_code_header_tag" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_header_compare" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderRejectedState" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeaderDispatchEnd" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttHeader_reject_steps" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeader_accept_steps" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeader_scan_steps" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderDispatch_steps" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttOrdinary_nosvd_prefix_of_running" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderDispatch_run_at" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderDispatch_fields_at" "NLA.Proofs.TR04.MachineTTHeaderDispatch" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_255" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_256" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_257" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_258" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_259" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_260" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_261" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_262" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_263" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_264" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_265" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_266" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_267" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_268" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_269" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_270" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_271" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_272" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_273" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_274" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_275" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_276" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_277" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_278" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_279" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_280" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_281" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_282" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_283" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_284" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_285" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_286" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_forward_394" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetupCells" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardSetupNaturalPrefix" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardSetupMiddle" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardSetupEnd" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_first" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_second" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_third" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_fourth" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_steps" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_run_at" "NLA.Proofs.TR04.MachineTTForwardScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardFirstPointerState" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardChildPointerState" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardLevelEnd" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardFirstEnd" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardChildEnd" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardFirst_pointer_steps" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardChild_pointer_steps" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardLevel_steps" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardFirst_return_steps" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardChild_return_steps" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardFirst_return_at" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardChild_return_at" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTForwardReturnStable" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardFirstEnd_fields" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardChildEnd_fields" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardFirstEnd_natural" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardChildEnd_natural" "NLA.Proofs.TR04.MachineTTForwardReturn" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyCellTime" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyRowTime" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyTime" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyStart" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyStart_eq_row" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_exists_trace" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_cell" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_cells" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_row_setup" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_row_exit" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_row" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_rows" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyFinalState" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_exit" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_trace_result" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_trace_product" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_trace_cost" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyTime_le_cubic" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_run" "NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyReturnTime" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyReturnState" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "definition"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_return_step" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_return" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyReturnState_product" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyReturnTime_le_cubic" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.matrixMultiplyProgram_nohalt" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_run_at" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.matrixMultiply_product_at" "NLA.Proofs.TR04.MachineMatrixMultiplyCallable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.splitIndex" "NLA.Proofs.TR04.Reshape" "public" "definition"
#audit_named "NLA.Proofs.TR04.splitIndex_join" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.join_splitIndex" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.joinEquiv" "NLA.Proofs.TR04.Reshape" "public" "definition"
#audit_named "NLA.Proofs.TR04.unfoldLinearEquiv" "NLA.Proofs.TR04.Reshape" "public" "definition"
#audit_named "NLA.Proofs.TR04.unfoldContinuousLinearEquiv" "NLA.Proofs.TR04.Reshape" "public" "definition"
#audit_named "NLA.Proofs.TR04.unfoldLinearEquiv_apply" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.continuous_unfold" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.unfold_zero" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.unfold_add" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.unfold_smul" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.unfold_injective" "NLA.Proofs.TR04.Reshape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.sum_unfold_indices" "NLA.Proofs.TR04.ReshapeFrobenius" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum" "NLA.Proofs.TR04.ReshapeFrobenius" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Index" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.indexFintype" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.Tensor" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.splitIndex" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.joinIndex" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.joinIndex_zero" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.join_splitIndex" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.split_joinIndex" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.splitEquiv" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.error" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_nonneg" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_unfold" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold_zero" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold_sub" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_unfold" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_zero" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_zero_right" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_nonneg" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.card_index" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.modeList" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.length_modeList" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv" "NLA.Proofs.TR04.TensorFormat" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_error_eq" "NLA.Proofs.TR04.TensorFormat" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.OrthonormalColumns" "NLA.Proofs.TR04.SVDEnergy" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.transpose_mul_eq_one" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.orthonormalColumns_submatrix" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.orthonormalColumns_inner" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.orthonormalColumns_sum_sq" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixEnergy" "NLA.Proofs.TR04.SVDEnergy" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.synthesis" "NLA.Proofs.TR04.SVDEnergy" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_eq_synthesis" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.synthesis_energy" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_energy" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.synthesis_sub" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_error_energy" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.truncate" "NLA.Proofs.TR04.SVDEnergy" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.tailEnergy" "NLA.Proofs.TR04.SVDEnergy" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_truncate_error" "NLA.Proofs.TR04.SVDEnergy" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.firstMatrix" "NLA.Proofs.TR04.TensorCompression" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv" "NLA.Proofs.TR04.TensorCompression" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.actFirst" "NLA.Proofs.TR04.TensorCompression" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.contract" "NLA.Proofs.TR04.TensorCompression" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.lift" "NLA.Proofs.TR04.TensorCompression" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actFirst_zero" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actFirst_sub" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actFirst_comp" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actFirst_one" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.contract_lift" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_firstMatrix" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_lift" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_lift" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.inner" "NLA.Proofs.TR04.TensorCompression" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_add" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.inner_contract_lift" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.residual_inner_lift" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_lift_decomposition" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_contract_le" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_contract_le" "NLA.Proofs.TR04.TensorCompression" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.prefixAction" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.headIndexEquiv" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_one" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le" "NLA.Proofs.TR04.TensorCompressionRanks" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_reindex" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_reindex" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.merge" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.merge_apply" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_merge" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_merge" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold_merge" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_merge" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.projected_error_eq" "NLA.Proofs.TR04.TensorCompressionMerge" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.truncate_rank_le" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixEnergy_nonneg" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixEnergy_entry_sq_le" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixEnergy_eq_zero_iff" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixError_eq_zero_iff" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_zero_tail_iff_truncate" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.tailEnergy_nonneg" "NLA.Proofs.TR04.SVDRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.prefixEnergy" "NLA.Proofs.TR04.SVDWeights" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.weightDefect" "NLA.Proofs.TR04.SVDWeights" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.prefix_count" "NLA.Proofs.TR04.SVDWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weighted_prefix_defect" "NLA.Proofs.TR04.SVDWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weightDefect_nonneg" "NLA.Proofs.TR04.SVDWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weighted_prefix_le" "NLA.Proofs.TR04.SVDWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weighted_prefix_eq_support" "NLA.Proofs.TR04.SVDWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixColumn" "NLA.Proofs.TR04.SVDProjection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.projectMatrix" "NLA.Proofs.TR04.SVDProjection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.matrixColumn_projectMatrix" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixColumn_sub" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixEnergy_eq_sum_column_norm" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectMatrix_energy_decomposition" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectMatrix_error_decomposition" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectMatrix_error_le" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectMatrix_error_eq_iff" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.exists_basis_of_orthonormalColumns" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projection_norm_sq_basis_sum" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectionWeight" "NLA.Proofs.TR04.SVDProjection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.projectionWeight_nonneg" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectionWeight_le_one" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_projectionWeight" "NLA.Proofs.TR04.SVDProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.right_synthesis_energy" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.matrixColumn_synthesis" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_project_energy" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_fin_prefix_le" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_svd_projectionWeight_le" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.singularSquares_antitone" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.prefix_add_tail" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_of_length_le" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.columnSpace" "NLA.Proofs.TR04.SVDEckartYoung" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.matrixColumn_mem_columnSpace" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.finrank_columnSpace" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_eckartYoung" "NLA.Proofs.TR04.SVDEckartYoung" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectionWeight_eq_one_iff" "NLA.Proofs.TR04.SVDEckartEquality" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectionWeight_eq_zero_iff" "NLA.Proofs.TR04.SVDEckartEquality" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq" "NLA.Proofs.TR04.SVDEckartEquality" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.thresholdDefect" "NLA.Proofs.TR04.SVDThresholdWeights" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.prefix_count_of_le" "NLA.Proofs.TR04.SVDThresholdWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weighted_threshold_defect" "NLA.Proofs.TR04.SVDThresholdWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.thresholdDefect_nonneg" "NLA.Proofs.TR04.SVDThresholdWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weighted_threshold_le" "NLA.Proofs.TR04.SVDThresholdWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.weighted_threshold_eq_support" "NLA.Proofs.TR04.SVDThresholdWeights" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_threshold" "NLA.Proofs.TR04.SVDEckartThreshold" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_last_retained" "NLA.Proofs.TR04.SVDEckartThreshold" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_iff" "NLA.Proofs.TR04.SVDConsequences" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_rank_le_iff_tail_zero" "NLA.Proofs.TR04.SVDConsequences" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_truncate_best" "NLA.Proofs.TR04.SVDConsequences" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_positive_tail" "NLA.Proofs.TR04.SVDConsequences" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients" "NLA.Proofs.TR04.SVDFrameProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_prefix_projection" "NLA.Proofs.TR04.SVDFrameProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffixSize" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffixEquiv" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.denseFirst" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_denseFirst" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_denseFirst" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.denseFirst_sub" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.cappedRank" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.prefixFrame" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le" "NLA.Proofs.TR04.TensorCompressionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.RankFeasible" "NLA.Proofs.TR04.TTCompletion" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.stepRank" "NLA.Proofs.TR04.TTCompletion" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.stepFrame" "NLA.Proofs.TR04.TTCompletion" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.stepInput" "NLA.Proofs.TR04.TTCompletion" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.stepOutput" "NLA.Proofs.TR04.TTCompletion" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.Completion" "NLA.Proofs.TR04.TTCompletion" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TensorFormat.completion_exists" "NLA.Proofs.TR04.TTCompletion" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract" "NLA.Proofs.TR04.TTCompletion" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.completion_feasible" "NLA.Proofs.TR04.TTCompletion" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.take_ofFn_modes" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalCut_le" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalRowEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalColEquiv" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_join" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.unfold_original" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_unfold_original" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalRanks" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_feasible_iff" "NLA.Proofs.TR04.TensorCompressionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixIndexEquiv" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixOffset" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixOffset_lt" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.cardToProdEquiv" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.prod_modeList" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorSuffixSize" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorOffset" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixOffset_vector" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_radixOffset" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize" "NLA.Proofs.TR04.TensorCompressionRadix" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.validSVD_reindex_columns" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixDenseFirst" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.suffixPermutation" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixDenseFirst_eq_reindex" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.denseFirst_eq_reindex_radix" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.rank_radixDenseFirst" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.energy_radixDenseFirst" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radix_validSVD_to_denseFirst" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.completion_step_radix" "NLA.Proofs.TR04.TensorCompressionRadixSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.mode_suffix_dvd_prod" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_pos" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorOffset_cons" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.vectorOffset_digit" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_decode_offset" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixOffset_decode" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.denseToProdEquiv" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv_offset" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_offset_decode" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_offset_injective" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_inputMemory_tensor_cell" "NLA.Proofs.TR04.TensorCompressionRadixDecode" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.StoresTensor" "NLA.Proofs.TR04.MachineTensorMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.StoresFrame" "NLA.Proofs.TR04.MachineTensorMemory" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.tensor_suffixSize_eq_prod" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixOffset_radixSuffixEquiv" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixDenseFirst_actFirst" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.StoresTensor.memory_eq" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesFrame_prefix" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.StoresFrame.memory_eq" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.storesTensor_original" "NLA.Proofs.TR04.MachineTensorMemory" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actMultiplyData" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.contractMultiplyData" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.liftMultiplyData" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.actMultiplyData_left" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actMultiplyData_right" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.actMultiplyData_product" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe" "NLA.Proofs.TR04.MachineTensorMultiplyData" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.contract_run_at" "NLA.Proofs.TR04.MachineTensorMultiplyTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.lift_run_at" "NLA.Proofs.TR04.MachineTensorMultiplyTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTForwardRegisters" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttForwardScratch" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_relates" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMatrix_natural_outside" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMatrix_real_outside" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttNaturalFold_outside" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_natural_outside" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForwardSetup_tag" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForward_contract_at" "NLA.Proofs.TR04.MachineTTForwardCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTForwardStable" "NLA.Proofs.TR04.MachineTTForward" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTForwardResult" "NLA.Proofs.TR04.MachineTTForward" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TTForwardResult.currentStored" "NLA.Proofs.TR04.MachineTTForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTForwardResult.metadata" "NLA.Proofs.TR04.MachineTTForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTForwardResult.mergedStored" "NLA.Proofs.TR04.MachineTTForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForward_first_at" "NLA.Proofs.TR04.MachineTTForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttForward_child_at" "NLA.Proofs.TR04.MachineTTForward" "public" "theorem"

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 255 = .copyNat (⟨4,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨256,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_255 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 256 = .copyNat (⟨5,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨257,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_256 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 257 = .copyNat (⟨6,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨258,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_257 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 258 = .copyNat (⟨7,by decide⟩ : Fin 128) (⟨86,by decide⟩ : Fin 128) (⟨259,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_258 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 259 = .copyNat (⟨8,by decide⟩ : Fin 128) (⟨85,by decide⟩ : Fin 128) (⟨260,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_259 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 260 = .copyNat (⟨9,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨261,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_260 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 261 = .copyNat (⟨10,by decide⟩ : Fin 128) (⟨94,by decide⟩ : Fin 128) (⟨262,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_261 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 262 = .copyNat (⟨11,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨263,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_262 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 263 = .copyNat (⟨12,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨264,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_263 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 264 = .copyNat (⟨13,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨265,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_264 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 265 = .copyNat (⟨14,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨266,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_265 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 266 = .copyNat (⟨15,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨267,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_266 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 267 = .copyNat (⟨16,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨268,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_267 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 268 = .copyNat (⟨17,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨269,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_268 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 269 = .copyNat (⟨18,by decide⟩ : Fin 128) (⟨88,by decide⟩ : Fin 128) (⟨270,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_269 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 270 = .copyNat (⟨19,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨271,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_270 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 271 = .copyNat (⟨20,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨272,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_271 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 272 = .copyNat (⟨97,by decide⟩ : Fin 128) (⟨108,by decide⟩ : Fin 128) (⟨273,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_272 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 273 = .jump (⟨11,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_273 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 274 = .copyNat (⟨89,by decide⟩ : Fin 128) (⟨69,by decide⟩ : Fin 128) (⟨275,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_274 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 275 = .copyNat (⟨90,by decide⟩ : Fin 128) (⟨70,by decide⟩ : Fin 128) (⟨276,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_275 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 276 = .jump (⟨281,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_276 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 277 = .copyNat (⟨123,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨278,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_277 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 278 = .copyNat (⟨89,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨279,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_278 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 279 = .copyNat (⟨90,by decide⟩ : Fin 128) (⟨123,by decide⟩ : Fin 128) (⟨280,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_279 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 280 = .jump (⟨281,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_280 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 281 = .copyNat (⟨100,by decide⟩ : Fin 128) (⟨86,by decide⟩ : Fin 128) (⟨282,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_281 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 282 = .increment (⟨84,by decide⟩ : Fin 128) (⟨283,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_282 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 283 = .copyNat (⟨110,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨284,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_283 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 284 = .decrement (⟨110,by decide⟩ : Fin 128) (⟨285,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_284 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 285 = .lessNat (⟨84,by decide⟩ : Fin 128) (⟨110,by decide⟩ : Fin 128) (⟨208,by decide⟩ : Fin 512) (⟨286,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_285 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 286 = .decrement (⟨84,by decide⟩ : Fin 128) (⟨287,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_286 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 394 = .equalNat (⟨97,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨277,by decide⟩ : Fin 512) (⟨341,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_forward_394 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label = 255) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[6] s = ttForwardSetupMiddle s 6 261 (by decide) := by
  exact @NLA.Proofs.TR04.ttForwardSetup_first s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttForwardSetupMiddle s 6 261 (by decide)) =
      ttForwardSetupMiddle s 12 267 (by decide) := by
  exact @NLA.Proofs.TR04.ttForwardSetup_second s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttForwardSetupMiddle s 12 267 (by decide)) =
      ttForwardSetupMiddle s 18 273 (by decide) := by
  exact @NLA.Proofs.TR04.ttForwardSetup_third s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) :
    ordinaryStep ttProgram (ttForwardSetupMiddle s 18 273 (by decide)) = ttForwardSetupEnd s := by
  exact @NLA.Proofs.TR04.ttForwardSetup_fourth s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label = 255) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[19] s = ttForwardSetupEnd s := by
  exact @NLA.Proofs.TR04.ttForwardSetup_steps s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 255) (hs : (trace.state offset).status = .running) :
    trace.state (offset+19)=ttForwardSetupEnd (trace.state offset) ∧
      CostThrough ttProgram trace (offset+19)≤CostThrough ttProgram trace offset+19 := by
  exact @NLA.Proofs.TR04.ttForwardSetup_run_at start trace ht offset hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=0) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[4] s=ttForwardFirstPointerState s := by
  exact @NLA.Proofs.TR04.ttForwardFirst_pointer_steps s hl hs htag hz
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=1)
    (hz : s.natural 127=0) (ho : s.natural 126=1) :
    (ordinaryStep ttProgram)^[6] s=ttForwardChildPointerState s := by
  exact @NLA.Proofs.TR04.ttForwardChild_pointer_steps s hl hs htag hz ho
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label=281) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[5] s=ttForwardLevelEnd s := by
  exact @NLA.Proofs.TR04.ttForwardLevel_steps s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=0) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[9] s=ttForwardFirstEnd s := by
  exact @NLA.Proofs.TR04.ttForwardFirst_return_steps s hl hs htag hz
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=1)
    (hz : s.natural 127=0) (ho : s.natural 126=1) :
    (ordinaryStep ttProgram)^[11] s=ttForwardChildEnd s := by
  exact @NLA.Proofs.TR04.ttForwardChild_return_steps s hl hs htag hz ho
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=32) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=0) (hz : (trace.state offset).natural 127=0) :
    trace.state (offset+9)=ttForwardFirstEnd (trace.state offset) ∧
    CostThrough ttProgram trace (offset+9)≤CostThrough ttProgram trace offset+9 := by
  exact @NLA.Proofs.TR04.ttForwardFirst_return_at start trace ht offset hl hs htag hz
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=32) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=1) (hz : (trace.state offset).natural 127=0)
    (ho : (trace.state offset).natural 126=1) :
    trace.state (offset+11)=ttForwardChildEnd (trace.state offset) ∧
    CostThrough ttProgram trace (offset+11)≤CostThrough ttProgram trace offset+11 := by
  exact @NLA.Proofs.TR04.ttForwardChild_return_at start trace ht offset hl hs htag hz ho
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) :
    (ttForwardFirstEnd s).label=(if s.natural 84+1<s.natural 0-1 then 208 else 286) ∧
    (ttForwardFirstEnd s).natural 89=s.natural 69 ∧
    (ttForwardFirstEnd s).natural 90=s.natural 70 ∧
    (ttForwardFirstEnd s).natural 100=s.natural 86 ∧
    (ttForwardFirstEnd s).natural 84=s.natural 84+1 ∧
    (ttForwardFirstEnd s).natural 110=s.natural 0-1 ∧
    (ttForwardFirstEnd s).memory=s.memory ∧ (ttForwardFirstEnd s).real=s.real := by
  exact @NLA.Proofs.TR04.ttForwardFirstEnd_fields s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) :
    (ttForwardChildEnd s).label=(if s.natural 84+1<s.natural 0-1 then 208 else 286) ∧
    (ttForwardChildEnd s).natural 89=s.natural 90 ∧
    (ttForwardChildEnd s).natural 90=s.natural 89 ∧
    (ttForwardChildEnd s).natural 100=s.natural 86 ∧
    (ttForwardChildEnd s).natural 84=s.natural 84+1 ∧
    (ttForwardChildEnd s).natural 110=s.natural 0-1 ∧
    (ttForwardChildEnd s).memory=s.memory ∧ (ttForwardChildEnd s).real=s.real := by
  exact @NLA.Proofs.TR04.ttForwardChildEnd_fields s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (i : Fin 128) (hi : TTForwardReturnStable i) :
    (ttForwardFirstEnd s).natural i=s.natural i := by
  exact @NLA.Proofs.TR04.ttForwardFirstEnd_natural s i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (i : Fin 128) (hi : TTForwardReturnStable i) :
    (ttForwardChildEnd s).natural i=s.natural i := by
  exact @NLA.Proofs.TR04.ttForwardChildEnd_natural s i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram)
    (m q : ℕ) (ns : List ℕ) (stride frame input output tag : ℕ)
    (hr : TTForwardRegisters s m q (suffixSize ns) stride frame input output tag) :
    ttMatrixEmbedding.Relates (matrixMultiplyRowState
      (contractMultiplyData s.memory m q ns frame stride input output) 0 (ttForwardScratch s))
      (ttForwardSetupEnd s) := by
  exact @NLA.Proofs.TR04.ttForwardSetup_relates s m q ns stride frame input output tag hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (i : Fin 128) (hi : (i.val < 4) ∨ (21 ≤ i.val)) :
    ∀ j, i≠ttMatrixEmbedding.naturals j := by
  exact @NLA.Proofs.TR04.ttMatrix_natural_outside i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (i : Fin 16) (hi : (i.val < 2) ∨ (5 ≤ i.val)) :
    ∀ j, i≠ttMatrixEmbedding.reals j := by
  exact @NLA.Proofs.TR04.ttMatrix_real_outside i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (cells : List (Fin 128 × ℕ)) (old : Fin 128 → ℕ) (i : Fin 128)
    (h : ∀ cell∈cells,i≠cell.1) :
    cells.foldl (fun regs cell => Function.update regs cell.1 cell.2) old i=old i := by
  exact @NLA.Proofs.TR04.ttNaturalFold_outside cells old i h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (i : Fin 128)
    (hi : (i.val < 4) ∨ (21 ≤ i.val)) (hi97 : i≠97) :
    (ttForwardSetupEnd s).natural i=s.natural i := by
  exact @NLA.Proofs.TR04.ttForwardSetup_natural_outside s i hi hi97
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    (ttForwardSetupEnd s).natural 97=s.natural 108 := by
  exact @NLA.Proofs.TR04.ttForwardSetup_tag s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output tag : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output tag)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+19+matrixMultiplyReturnTime p
    (trace.state time).label=32 ∧ (trace.state time).status=.running ∧
    StoresTensor (trace.state time).memory output (q::ns) (contract Q A) ∧
    StoresTensor (trace.state time).memory input (m::ns) A ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, ¬(output≤a ∧ a<output+q*suffixSize ns) →
      (trace.state time).memory a=(trace.state offset).memory a) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3 ∧
    (∀ i : Fin 16, (i.val < 2) ∨ (5 ≤ i.val) → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, ((i.val < 4) ∨ (21 ≤ i.val)) → i≠97 →
      (trace.state time).natural i=(trace.state offset).natural i) ∧
    (trace.state time).natural 97=tag := by
  exact @NLA.Proofs.TR04.ttForward_contract_at start trace ht offset m q ns stride frame input output tag hl hs hr hq Q hQ A hA hQblock hAblock
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)}
    (h : TTForwardResult old final m q ns stride frame input output next Q A) :
    StoresTensor final.memory (final.natural 89) (q::ns) (contract Q A) := by
  exact @NLA.Proofs.TR04.TTForwardResult.currentStored old final m q ns stride frame input output next Q A h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)}
    (h : TTForwardResult old final m q ns stride frame input output next Q A)
    (base count : ℕ) (hd : DisjointBlocks base count output (q*suffixSize ns)) :
    ∀ a, base≤a ∧ a<base+count → final.memory a=old.memory a := by
  exact @NLA.Proofs.TR04.TTForwardResult.metadata old final m q ns stride frame input output next Q A h base count hd
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {old final : State ttProgram}
    {m q n : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::n::ns)}
    (h : TTForwardResult old final m q (n::ns) stride frame input output next Q A) :
    StoresTensor final.memory (final.natural 89) ((q*n)::ns)
      (merge q n ns (contract Q A)) := by
  exact @NLA.Proofs.TR04.TTForwardResult.mergedStored old final m q n ns stride frame input output next Q A h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 0)
    (hw : (trace.state offset).natural 69=output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+19+matrixMultiplyReturnTime p+9
    TTForwardResult (trace.state offset) (trace.state time) m q ns stride frame input output
      ((trace.state offset).natural 70) Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+9 := by
  exact @NLA.Proofs.TR04.ttForward_first_at start trace ht offset m q ns stride frame input output hl hs hr hw hq Q hQ A hA hQblock hAblock
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 1)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+19+matrixMultiplyReturnTime p+11
    TTForwardResult (trace.state offset) (trace.state time) m q ns stride frame input output input Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+11 := by
  exact @NLA.Proofs.TR04.ttForward_child_at start trace ht offset m q ns stride frame input output hl hs hr hq Q hQ A hA hQblock hAblock
end NLA.Proofs.TR04

namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

-- The actual first contraction's terminal-level branch reaches the reverse
-- entry286 before its decrement and stores the computed contraction.
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 0)
    (hw : (trace.state offset).natural 69=output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns))
    (hlast : ¬((trace.state offset).natural 84+1<(trace.state offset).natural 0-1)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let t := offset+19+matrixMultiplyReturnTime p+9
    (trace.state t).label=286 ∧ (trace.state t).status=.running ∧
      StoresTensor (trace.state t).memory ((trace.state t).natural 89) (q::ns) (contract Q A) ∧
      (trace.state t).natural 90=(trace.state offset).natural 70 ∧
      CostThrough ttProgram trace t≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+9 := by
  obtain ⟨h,hcost⟩ := ttForward_first_at ht offset m q ns stride frame input output hl hs hr hw hq Q hQ A hA hQblock hAblock
  refine ⟨?_,h.running,h.currentStored,h.nextBuffer,hcost⟩
  simpa only [if_neg hlast] using h.label

-- The actual child return swaps the two buffers and its tensor can be merged
-- by the literal radix identity without executing a copy or assuming a result.
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q n : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize (n::ns)) stride frame input output 1)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::n::ns)) (hA : StoresTensor (trace.state offset).memory input (m::n::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize (n::ns)))
    (hAblock : DisjointBlocks input (m*suffixSize (n::ns)) output (q*suffixSize (n::ns))) :
    let p := contractMultiplyData (trace.state offset).memory m q (n::ns) frame stride input output
    let t := offset+19+matrixMultiplyReturnTime p+11
    (trace.state t).natural 89=output ∧ (trace.state t).natural 90=input ∧
      StoresTensor (trace.state t).memory ((trace.state t).natural 89) ((q*n)::ns)
        (merge q n ns (contract Q A)) ∧
      CostThrough ttProgram trace t≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize (n::ns)+1)^3+11 := by
  obtain ⟨h,hcost⟩ := ttForward_child_at ht offset m q (n::ns) stride frame input output hl hs hr hq Q hQ A hA hQblock hAblock
  exact ⟨h.current,h.nextBuffer,h.mergedStored,hcost⟩

end NLA.Proofs.TR04

end
