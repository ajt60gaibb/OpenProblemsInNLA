import NLA.Proofs.TR04.MachineTTFirstSelectionFamily

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
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_nine_steps" "NLA.Proofs.TR04.MachineThresholdScanExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_iterations" "NLA.Proofs.TR04.MachineThresholdScanExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdScanReturnState" "NLA.Proofs.TR04.MachineThresholdScanTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_return" "NLA.Proofs.TR04.MachineThresholdScanTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdScanProgram_trace_result" "NLA.Proofs.TR04.MachineThresholdScanTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run" "NLA.Proofs.TR04.MachineThresholdScanTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_at" "NLA.Proofs.TR04.MachineThresholdScanTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_values" "NLA.Proofs.TR04.MachineThresholdScanTrace" "public" "theorem"
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
#audit_named "NLA.Proofs.TR04.SVD.singularSubspace" "NLA.Proofs.TR04.SVDResidual" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.singularSubspace_le" "NLA.Proofs.TR04.SVDResidual" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le" "NLA.Proofs.TR04.SVDResidual" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual" "NLA.Proofs.TR04.SVDResidual" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients" "NLA.Proofs.TR04.SVDFrameProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_prefix_projection" "NLA.Proofs.TR04.SVDFrameProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.orthonormal_matrixColumns" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.finrank_singularSubspace" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.starProjection_singularSubspace" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_selected_energy" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_selected_error" "NLA.Proofs.TR04.SVDSelected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicWindow" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.cyclicTranslate" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.cyclicDifference" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.prefixSubtypeEquiv" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.card_cyclicWindow" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.average_cyclicWindow_energy" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average" "NLA.Proofs.TR04.SVDCyclicWindows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal" "NLA.Proofs.TR04.SVDSelectedProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.norm_singularSubspace_projection" "NLA.Proofs.TR04.SVDSelectedProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.singularCoordinateEnergy" "NLA.Proofs.TR04.SVDSelectedProjection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg" "NLA.Proofs.TR04.SVDSelectedProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy" "NLA.Proofs.TR04.SVDSelectedProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le" "NLA.Proofs.TR04.SVDSelectedProjection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns" "NLA.Proofs.TR04.SVDProjectionRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix" "NLA.Proofs.TR04.SVDProjectionRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le" "NLA.Proofs.TR04.SVDProjectionRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank" "NLA.Proofs.TR04.SVDProjectionRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_selected_projection_le_card" "NLA.Proofs.TR04.SVDProjectionRank" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.selectedFrame" "NLA.Proofs.TR04.SVDSelectedFrame" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame" "NLA.Proofs.TR04.SVDSelectedFrame" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.orthonormalColumns_rank" "NLA.Proofs.TR04.SVDSelectedFrame" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_selectedFrame" "NLA.Proofs.TR04.SVDSelectedFrame" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.tieEmbedding" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.tieEmbedding_injective" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.prefixDirections" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.tieDirections" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.windowDirections" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.tieSelection" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.prefix_window_disjoint" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.card_tieSelection" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_tieSelection" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_all_tieSelections" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_indicator_finset" "NLA.Proofs.TR04.SVDCyclicSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.directionSubspace" "NLA.Proofs.TR04.SVDTieProjectors" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.directionSubspace_project_energy" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_directionFrame" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_directionProjection_le" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_tieSelectionFrame" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.average_tieSelection_project_energy" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le" "NLA.Proofs.TR04.SVDTieProjectors" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin" "NLA.Proofs.TR04.SVDTieError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_prefixDirections" "NLA.Proofs.TR04.SVDTieError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.prefixEnergy_tie_split" "NLA.Proofs.TR04.SVDTieError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block" "NLA.Proofs.TR04.SVDTieError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_tieSelection_error" "NLA.Proofs.TR04.SVDTieError" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.card_filter_fin_lt" "NLA.Proofs.TR04.SVDTieStructure" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card" "NLA.Proofs.TR04.SVDTieStructure" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure" "NLA.Proofs.TR04.SVDTieStructure" "public" "inductive"
#audit_named "NLA.Proofs.TR04.SVD.exists_tieStructure" "NLA.Proofs.TR04.SVDTieStructure" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.tied_pos" "NLA.Proofs.TR04.SVDTieStructure" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.equal_embedding" "NLA.Proofs.TR04.SVDTieStructure" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.mem_prefixDirections_iff" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.tieSelection_val_lt" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.above_subspace" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.first_error" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.frame_rank" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual" "NLA.Proofs.TR04.SVDTieGate" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.prefix_weights_eq_one" "NLA.Proofs.TR04.SVDTieFull" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights" "NLA.Proofs.TR04.SVDTieFull" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero" "NLA.Proofs.TR04.SVDTieFull" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual" "NLA.Proofs.TR04.SVDTieFull" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.starProjection_span_orthonormal" "NLA.Proofs.TR04.SVDFrameSpace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.frameSpace" "NLA.Proofs.TR04.SVDFrameSpace" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.orthonormal_frameColumns" "NLA.Proofs.TR04.SVDFrameSpace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.frame_projectMatrix" "NLA.Proofs.TR04.SVDFrameSpace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix" "NLA.Proofs.TR04.SVDFrameSpace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.exists_directionFrame" "NLA.Proofs.TR04.SVDFrameSpace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.exists_frame" "NLA.Proofs.TR04.SVDFrameSpace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicColumnIndex" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.cyclicColumnIndex_val" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicFrame" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicFrame_space" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicFrame_rank" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.cyclicFrame_projection" "NLA.Proofs.TR04.SVDExplicitCyclic" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.countedTieStructure" "NLA.Proofs.TR04.SVDExplicitTie" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.countedTieStructure_above" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.countedTieStructure_tied" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.countedTieStructure_take" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitIndex" "NLA.Proofs.TR04.SVDExplicitTie" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitFrame" "NLA.Proofs.TR04.SVDExplicitTie" "public" "definition"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank" "NLA.Proofs.TR04.SVDExplicitTie" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdCard_filter_range_fin" "NLA.Proofs.TR04.MachineThresholdScanSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdCard_filter_fin_interval" "NLA.Proofs.TR04.MachineThresholdScanSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.thresholdCounts_countedTieStructure" "NLA.Proofs.TR04.MachineThresholdScanSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_counted" "NLA.Proofs.TR04.MachineThresholdScanSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_nonzero_reals" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.code168" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code169" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code170" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code171" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code172" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code173" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code174" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code175" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code176" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code177" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code178" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code179" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code180" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code181" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code182" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code183" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code184" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code185" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code186" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code187" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code188" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne73_122" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne127_122" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne7_13" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne13_7" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne80_42" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne73_42" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne73_43" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne47_77" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne48_77" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne48_78" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne78_77" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ne78_79" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstPrefixResult" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstThresholdRead" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstThresholdEntry" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstCountResult" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_prefix_five" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_large_six" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_read_seven" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_nonpositive_twelve" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_setup_four" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_return_six" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_not_svd" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.code88" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_prefix_safe" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_large_safe" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_read_safe" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_nonpositive_safe" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_setup_safe" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_return_safe" "NLA.Proofs.TR04.MachineTTFirstSelectionScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTFirstProtected" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTFirstPreserves" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstPreserves_trans" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstPrefix_preserves" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRead_preserves" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstEntry_preserves" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstCount_preserves" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstThresholdAux" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstThreshold_relates" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstThreshold_outside" "NLA.Proofs.TR04.MachineTTFirstSelectionTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_large_run" "NLA.Proofs.TR04.MachineTTFirstSelectionRun" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_nonpositive_run" "NLA.Proofs.TR04.MachineTTFirstSelectionRun" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_positive_run" "NLA.Proofs.TR04.MachineTTFirstSelectionRun" "public" "theorem"
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
#audit_named "NLA.Proofs.TR04.TensorFormat.completion_comparator_bound" "NLA.Proofs.TR04.TTCompletionBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.projected_completion_bound" "NLA.Proofs.TR04.TTCompletionBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.projected_completion_feasible" "NLA.Proofs.TR04.TTCompletionProjected" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.exists_projected_completion" "NLA.Proofs.TR04.TTCompletionProjected" "public" "theorem"
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
#audit_named "NLA.Proofs.TR04.feasible_zero" "NLA.Proofs.TR04.Feasible" "public" "theorem"
#audit_named "NLA.Proofs.TR04.feasible_nonempty" "NLA.Proofs.TR04.Feasible" "public" "theorem"
#audit_named "NLA.Proofs.TR04.isClosed_matrix_rank_le" "NLA.Proofs.TR04.Feasible" "public" "theorem"
#audit_named "NLA.Proofs.TR04.isClosed_feasible" "NLA.Proofs.TR04.Feasible" "public" "theorem"
#audit_named "NLA.Proofs.TR04.continuous_frobeniusSq" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frobeniusSq_nonneg" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frobeniusSq_coordinate_le" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frobeniusSq_self" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frobeniusSq_eq_zero_iff" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.exists_feasible_minimizer" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.exists_optimum" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.optimum_nonneg" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.optimum_le_of_feasible" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.optimum_eq_zero_iff_feasible" "NLA.Proofs.TR04.Optimum" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.OriginalCompletion" "NLA.Proofs.TR04.TTCompletionOriginal" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_completion_exists" "NLA.Proofs.TR04.TTCompletionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_completion_feasible" "NLA.Proofs.TR04.TTCompletionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_completion_comparator_bound" "NLA.Proofs.TR04.TTCompletionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_completion_optimum_bound" "NLA.Proofs.TR04.TTCompletionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.original_completion_exact_of_optimum_zero" "NLA.Proofs.TR04.TTCompletionOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.error_eq_zero_iff" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.error_denseFirst" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_le" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_eq" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.error_projection_eq" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput" "NLA.Proofs.TR04.TTStrictBasics" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.IsMinimum" "NLA.Proofs.TR04.TTStrictBasics" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.exists_minimum" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_bound" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_strict_of_first_lt" "NLA.Proofs.TR04.TTStrictBasics" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.FirstFrames" "NLA.Proofs.TR04.TTStrictFrames" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames" "NLA.Proofs.TR04.TTStrictFrames" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames_first_error" "NLA.Proofs.TR04.TTStrictFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.exists_firstFrames" "NLA.Proofs.TR04.TTStrictFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.rank_denseFirst_le_first" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.family_first_error" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.family_projected_energy" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_feasible" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_bound" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.family_min_strict" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_exact_of_error_zero" "NLA.Proofs.TR04.TTStrictBound" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.exists_strict_family" "NLA.Proofs.TR04.TTStrictFamily" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_positive" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_large" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_nonpos" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_width" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec" "NLA.Proofs.TR04.TTStrictExplicitFrames" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTFirstChoice" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttFirstPrefixChoice" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstChoice" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTFirstSelected" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstChoice_count_pos" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstChoice_width" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_run" "NLA.Proofs.TR04.MachineTTFirstSelection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_svd_run" "NLA.Proofs.TR04.MachineTTFirstSelectionSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_eleven_steps" "NLA.Proofs.TR04.MachineFrameGatherExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_inner_iterations" "NLA.Proofs.TR04.MachineFrameGatherRows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_row_exit" "NLA.Proofs.TR04.MachineFrameGatherRows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_one_row" "NLA.Proofs.TR04.MachineFrameGatherRows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_rows" "NLA.Proofs.TR04.MachineFrameGatherRows" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherReturnState" "NLA.Proofs.TR04.MachineFrameGatherTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_return" "NLA.Proofs.TR04.MachineFrameGatherTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherProgram_trace_result" "NLA.Proofs.TR04.MachineFrameGatherTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.frameGather_run" "NLA.Proofs.TR04.MachineFrameGatherTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_at" "NLA.Proofs.TR04.MachineFrameGatherTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells" "NLA.Proofs.TR04.MachineFrameGatherTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMatrix" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.frameGatherMemory_matrix" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.tieGatherParameters" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.tieGatherParameters_valid" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.tieGatherParameters_width" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMatrix_tie" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.prefixGatherParameters" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.prefixGatherParameters_valid" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.frameGatherMatrix_prefix" "NLA.Proofs.TR04.MachineFrameGatherSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstGatherParameters" "NLA.Proofs.TR04.MachineTTFirstSelectionFamily" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTFirstChoiceRealizes" "NLA.Proofs.TR04.MachineTTFirstSelectionFamily" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstPrefix_realizes" "NLA.Proofs.TR04.MachineTTFirstSelectionFamily" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstChoice_realizes_explicit" "NLA.Proofs.TR04.MachineTTFirstSelectionFamily" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstSelection_svd_family" "NLA.Proofs.TR04.MachineTTFirstSelectionFamily" "public" "theorem"

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 184) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[5] s = ttFirstPrefixResult s := @NLA.Proofs.TR04.ttFirstSelection_prefix_five s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running)
    (hr : s.natural 105 < s.natural 80) :
    (ordinaryStep ttProgram)^[6] s = ttFirstPrefixResult s := @NLA.Proofs.TR04.ttFirstSelection_large_six s hl hs hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (ht : (s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    (ordinaryStep ttProgram)^[7] s = ttFirstThresholdRead s := @NLA.Proofs.TR04.ttFirstSelection_read_seven s hl hs hr ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (ht : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    (ordinaryStep ttProgram)^[12] s =
      ttFirstPrefixResult {ttFirstThresholdRead s with label := 184} := @NLA.Proofs.TR04.ttFirstSelection_nonpositive_twelve s hl hs hr ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 175) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[4] s = ttFirstThresholdEntry s := @NLA.Proofs.TR04.ttFirstSelection_setup_four s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 88) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[6] s = ttFirstCountResult s := @NLA.Proofs.TR04.ttFirstSelection_return_six s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (ha : s.label.val ≠ 167) (hb : s.label.val ≠ 237) :
    instructionIsSVD (ttProgram.code s.label) = false := @NLA.Proofs.TR04.ttFirstSelection_not_svd s ha hb
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 184) (hs : s.status = .running)  :
    ∀ k < 5, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := @NLA.Proofs.TR04.ttFirstSelection_prefix_safe s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running) (hr : s.natural 105 < s.natural 80) :
    ∀ k < 6, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := @NLA.Proofs.TR04.ttFirstSelection_large_safe s hl hs hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running) (hr : ¬s.natural 105 < s.natural 80) :
    ∀ k < 7, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := @NLA.Proofs.TR04.ttFirstSelection_read_safe s hl hs hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running) (hr : ¬s.natural 105 < s.natural 80) (ht : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    ∀ k < 12, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := @NLA.Proofs.TR04.ttFirstSelection_nonpositive_safe s hl hs hr ht
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 175) (hs : s.status = .running)  :
    ∀ k < 4, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := @NLA.Proofs.TR04.ttFirstSelection_setup_safe s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram)
    (hl : s.label = 88) (hs : s.status = .running)  :
    ∀ k < 6, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := @NLA.Proofs.TR04.ttFirstSelection_return_safe s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {s t u : State ttProgram}
    (h : TTFirstPreserves s t) (k : TTFirstPreserves t u) : TTFirstPreserves s u := @NLA.Proofs.TR04.ttFirstPreserves_trans s t u h k
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) : TTFirstPreserves s (ttFirstPrefixResult s) := @NLA.Proofs.TR04.ttFirstPrefix_preserves s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) : TTFirstPreserves s (ttFirstThresholdRead s) := @NLA.Proofs.TR04.ttFirstRead_preserves s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) : TTFirstPreserves s (ttFirstThresholdEntry s) := @NLA.Proofs.TR04.ttFirstEntry_preserves s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) : TTFirstPreserves s (ttFirstCountResult s) := @NLA.Proofs.TR04.ttFirstCount_preserves s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hs : s.status = .running) :
    ttThresholdEmbedding.Relates
      (thresholdScanStart s.memory ⟨s.natural 105, s.natural 80, s.natural 73⟩
        (s.memory (s.natural 73 + (s.natural 80 - 1))) (s.real 8) (ttFirstThresholdAux s))
      (ttFirstThresholdEntry (ttFirstThresholdRead s)) := @NLA.Proofs.TR04.ttFirstThreshold_relates s hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (aux : Fin 5 → ℕ)
    {start : State ttProgram} {trace : Trace ttProgram} (ht : LegalTrace ttProgram start trace)
    (offset : ℕ)
    (hs : ttThresholdEmbedding.Relates (thresholdScanStart memory P tau scratch aux) (trace.state offset))
    (j : Fin 128) (hj : 49 ≤ j.val) :
    (trace.state (offset + (9 * P.count + 6))).natural j = (trace.state offset).natural j := @NLA.Proofs.TR04.ttFirstThreshold_outside memory P tau scratch aux start trace ht offset hs j hj
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : s.natural 105 < s.natural 80) :
    trace.state (offset + 6) = ttFirstPrefixResult s ∧
      TTFirstPreserves s (trace.state (offset + 6)) ∧
      CostThrough ttProgram trace (offset + 6) ≤ CostThrough ttProgram trace offset + 6 := @NLA.Proofs.TR04.ttFirstSelection_large_run start trace ht offset s he hl hs hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (hz : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    trace.state (offset + 12) = ttFirstPrefixResult {ttFirstThresholdRead s with label := 184} ∧
      TTFirstPreserves s (trace.state (offset + 12)) ∧
      CostThrough ttProgram trace (offset + 12) ≤ CostThrough ttProgram trace offset + 12 := @NLA.Proofs.TR04.ttFirstSelection_nonpositive_run start trace ht offset s he hl hs hr hz
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (hz : (s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    let P : ThresholdScanParameters := ⟨s.natural 105, s.natural 80, s.natural 73⟩
    let tau := s.memory (s.natural 73 + (s.natural 80 - 1))
    let n := offset + (9 * P.count + 23)
    (trace.state n).label = 189 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural 77 = thresholdAboveCount s.memory P tau P.count ∧
      (trace.state n).natural 78 = thresholdTiedCount s.memory P tau P.count ∧
      (trace.state n).natural 79 = thresholdTakeCount s.memory P tau P.count ∧
      (trace.state n).natural 75 = thresholdTiedCount s.memory P tau P.count ∧
      TTFirstPreserves s (trace.state n) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset + (9 * P.count + 23) := @NLA.Proofs.TR04.ttFirstSelection_positive_run start trace ht offset s he hl hs hr hz
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (r cap : ℕ) (hr : 1 ≤ r) : 0 < (ttFirstChoice sigma hord r cap hr).count := @NLA.Proofs.TR04.ttFirstChoice_count_pos p sigma hord r cap hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (r : ℕ) (hr : 1 ≤ r) :
    (ttFirstChoice sigma hord r (min r p) hr).above +
      (ttFirstChoice sigma hord r (min r p) hr).take = min r p := @NLA.Proofs.TR04.ttFirstChoice_width p sigma hord r hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma) (r cap : ℕ) (hr : 1 ≤ r)
    (hp : s.natural 105 = p) (hrank : s.natural 80 = r) (hcap : s.natural 106 = cap)
    (hzero : s.natural 127 = 0)
    (hmem : ∀ k : Fin p, s.memory (s.natural 73 + k.val) = sigma k) :
    ∃ n : ℕ, n ≤ 9 * p + 23 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      TTFirstSelected (ttFirstChoice sigma hord r cap hr) (trace.state (offset + n)) ∧
      TTFirstPreserves s (trace.state (offset + n)) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset + (9 * p + 23) := @NLA.Proofs.TR04.ttFirstSelection_run start trace ht offset s he hl hs p sigma hord r cap hr hp hrank hcap hzero hmem
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 167) (hs : s.status = .running)
    (hp : s.natural 105 = min (s.natural 81) (s.natural 82))
    (hr : 1 ≤ s.natural 80) (hzero : s.natural 127 = 0)
    (hd : OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74)) :
    ∃ U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ,
    ∃ sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ,
    ∃ n : ℕ,
      ValidSVD (readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92)) U sigma V ∧
      n ≤ 9 * min (s.natural 81) (s.natural 82) + 24 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      (∃ hord : Antitone sigma, TTFirstSelected
        (ttFirstChoice sigma hord (s.natural 80) (s.natural 106) hr) (trace.state (offset + n))) ∧
      (trace.state (offset + n)).memory =
        writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) U sigma V ∧
      (∀ j : Fin 128, TTFirstProtected j → (trace.state (offset + n)).natural j = s.natural j) ∧
      readMatrix (trace.state (offset + n)).memory (s.natural 81) (s.natural 81) (s.natural 72) = U ∧
      (∀ k, (trace.state (offset + n)).memory (s.natural 73 + k.val) = sigma k) ∧
      readMatrix (trace.state (offset + n)).memory (s.natural 82) (s.natural 82) (s.natural 74) = V ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset +
        (s.natural 81 + s.natural 82 + 1)^3 + (9 * min (s.natural 81) (s.natural 82) + 23) := @NLA.Proofs.TR04.ttFirstSelection_svd_run start trace ht offset s he hl hs hp hr hzero hd
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
open TensorFormat.TTStrict
example {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r inputBase outputBase : ℕ) :
    TTFirstChoiceRealizes U (ttFirstPrefixChoice (min r (min m l))) (defaultFrames h r)
      inputBase outputBase := @NLA.Proofs.TR04.ttFirstPrefix_realizes m l B U sigma V h r inputBase outputBase
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
open TensorFormat.TTStrict
example {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (inputBase outputBase : ℕ) :
    TTFirstChoiceRealizes U (ttFirstChoice sigma h.2.2.2.1 r (min r (min m l)) hr)
      (explicitFirstFrames h r) inputBase outputBase := @NLA.Proofs.TR04.ttFirstChoice_realizes_explicit m l B U sigma V h r hr inputBase outputBase
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
open TensorFormat.TTStrict
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 167) (hs : s.status = .running)
    (hp : s.natural 105 = min (s.natural 81) (s.natural 82))
    (hr : 1 ≤ s.natural 80) (hzero : s.natural 127 = 0)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hd : OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74)) :
    ∃ U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ,
    ∃ sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ,
    ∃ hvalid : ValidSVD (readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92)) U sigma V,
    ∃ n : ℕ,
      n ≤ 9 * min (s.natural 81) (s.natural 82) + 24 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      TTFirstSelected (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
        (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr) (trace.state (offset + n)) ∧
      (∀ inputBase outputBase, TTFirstChoiceRealizes U
        (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
          (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr)
        (explicitFirstFrames hvalid (s.natural 80)) inputBase outputBase) ∧
      (trace.state (offset + n)).memory =
        writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) U sigma V ∧
      (∀ j : Fin 128, TTFirstProtected j → (trace.state (offset + n)).natural j = s.natural j) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset +
        (s.natural 81 + s.natural 82 + 1)^3 + (9 * min (s.natural 81) (s.natural 82) + 23) := @NLA.Proofs.TR04.ttFirstSelection_svd_family start trace ht offset s he hl hs hp hr hzero hcap hd
end NLA.Proofs.TR04

namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

-- Derive loop nonemptiness and the exact computed frame width from the actual
-- first-SVD phase endpoint for every legal reply, rather than assuming them.
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 167) (hs : s.status = .running)
    (hp : s.natural 105 = min (s.natural 81) (s.natural 82))
    (hr : 1 ≤ s.natural 80) (hzero : s.natural 127 = 0)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hd : OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74)) :
    ∃ n : ℕ, n ≤ 9 * min (s.natural 81) (s.natural 82) + 24 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      0 < (trace.state (offset + n)).natural 75 ∧
      (trace.state (offset + n)).natural 77 + (trace.state (offset + n)).natural 79 =
        min (s.natural 80) (min (s.natural 81) (s.natural 82)) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset +
        (s.natural 81 + s.natural 82 + 1)^3 + (9 * min (s.natural 81) (s.natural 82) + 23) := by
  obtain ⟨U, sigma, V, hvalid, n, hn, hlabel, hrun, hselected, _, _, _, hcost⟩ :=
    ttFirstSelection_svd_family ht offset s he hl hs hp hr hzero hcap hd
  refine ⟨n, hn, hlabel, hrun, ?_, ?_, hcost⟩
  · rw [hselected.2.2.2]
    exact ttFirstChoice_count_pos sigma hvalid.2.2.2.1 (s.natural 80)
      (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr
  · rw [hselected.1, hselected.2.2.1]
    exact ttFirstChoice_width sigma hvalid.2.2.2.1 (s.natural 80) hr

end NLA.Proofs.TR04

end
