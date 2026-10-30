import NLA.Proofs.TR04.MachineTTReverse

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
  logInfo m!"AUDITED_KIND {decl.toString} {expected.getString}"
  logInfo m!"AUDITED_ACTUAL {user.getString} {decl.toString} {visibility.getString}"
  elabCommand (← `(#assert_trust $(mkIdent `kernel) $(mkIdent decl)))
  elabCommand (← `(#print axioms $(mkIdent decl)))
  let axs ← liftCoreM <| collectAxioms decl
  let body := String.intercalate "," (axs.toList.map Name.toString)
  logInfo m!"AUDITED_AXIOMS {decl.toString} [{body}]"
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
#audit_named "NLA.Proofs.TR04.headerSingleReturnState" "NLA.Proofs.TR04.MachineHeaderProductSingle" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerSingle_after_decode" "NLA.Proofs.TR04.MachineHeaderProductSingle" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerSingle_return" "NLA.Proofs.TR04.MachineHeaderProductSingle" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.headerSingle_run_at" "NLA.Proofs.TR04.MachineHeaderProductSingle" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRangeValues" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerRangeProduct" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerRangeTime" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerRange_prefix_start" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRange_prefix_product" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRange_iterations" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRangeEntryState" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerRangeReturnState" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "definition"
#audit_named "NLA.Proofs.TR04.headerRange_entry_product" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRange_entry_eq" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRange_return_product" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRange_return" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRange_time_le" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.RoutineEmbedding.headerRange_run_at" "NLA.Proofs.TR04.MachineHeaderProductRange" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttInitScalar_nonzero_reals" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttInitScalar_labels" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInitScalar_naturals" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInitScalar_reals" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code144" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code145" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code146" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code147" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code148" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code149" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code150" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code151" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code152" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code153" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code154" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code155" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code156" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code157" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code158" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code159" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code160" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code161" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code162" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code163" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code164" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code165" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttInit_code166" "NLA.Proofs.TR04.MachineTTInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttModeSuffixEntry" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttModeSuffix_steps" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttColsRankEntry" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttColsRank_steps" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstMinRowsEnd" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstMinRows_steps" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstMinCapRowsEnd" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstMinCapRows_steps" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstMinCapColsEnd" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstMinCapCols_steps" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRankEnd" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstRank_steps" "NLA.Proofs.TR04.MachineTTInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout" "NLA.Proofs.TR04.TTMemoryLayout" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.ofShape" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.input" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.childV" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frames" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workA" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workB" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.store" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Fits" "NLA.Proofs.TR04.TTMemoryLayout" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.fits_same" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.fits_trans" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.disjoint_symm" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.disjoint_of_end_le" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.disjoint_fits" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.fits_address" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.square_capacity" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.rectangle_capacity" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_metadata" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_mem" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_fits" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint" "NLA.Proofs.TR04.TTMemoryLayout" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.header_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.input_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.input_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.childV_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_workA" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.before_work_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.work_buffers_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_candidate_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_candidate_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_metadata_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_work_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_rectangle_fits" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_rectangle_fits" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_rectangle_fits" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.writeSVD_preserves_disjoint_block" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_frame_disjoint" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame" "NLA.Proofs.TR04.TTMemoryLayoutProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.store_le_endAddress" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_before_store" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_before_store" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_before_store" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.prefix_address_lt_end" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_address_lt_end" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_address_lt_end" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_address_lt_end" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_le_cubic" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.ofShape_input" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.StageMetadata" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.Bounded" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value_le" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.frame_capacity" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.original_value_le_size" "NLA.Proofs.TR04.TTMemoryLayoutBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_nonzero_realRegisters" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_labels" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_naturals" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_reals" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code119" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code120" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code121" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code122" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code123" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code124" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code125" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code126" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code127" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code128" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code129" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code130" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code131" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code132" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code133" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code134" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code135" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code136" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code137" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code138" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code139" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code140" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code141" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code142" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_code143" "NLA.Proofs.TR04.MachineTTStartup" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ordinary_nosvd_prefix_of_running" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartupNatural" "NLA.Proofs.TR04.MachineTTStartup" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttStartupEnd" "NLA.Proofs.TR04.MachineTTStartup" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttStartupNaturalPrefix" "NLA.Proofs.TR04.MachineTTStartup" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttStartupMiddle" "NLA.Proofs.TR04.MachineTTStartup" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttStartup_first" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_second" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_third" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_fourth" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_steps" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTAllocationRegisters" "NLA.Proofs.TR04.MachineTTStartup" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttStartup_allocation" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_decoder" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_flags" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStartup_run_at" "NLA.Proofs.TR04.MachineTTStartup" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeader_outside_at" "NLA.Proofs.TR04.MachineTTHeaderCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderSingle_full_at" "NLA.Proofs.TR04.MachineTTHeaderCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderRange_full_at" "NLA.Proofs.TR04.MachineTTHeaderCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttAllocation_transfer" "NLA.Proofs.TR04.MachineTTHeaderCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttModeSuffix_relates" "NLA.Proofs.TR04.MachineTTHeaderCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttColsRank_relates" "NLA.Proofs.TR04.MachineTTHeaderCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttInitTrace_naturals" "NLA.Proofs.TR04.MachineTTInitializationTrace" "private" "theorem"
#audit_named "NLA.Proofs.TR04.TTInitKept" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTInitPreserves" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttInitPreserves_trans" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttInitPreserves_allocation" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttModeSuffix_preserves" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttColsRank_preserves" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRank_preserves" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderDispatch_preserves" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeader_preserves_of_outside" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttScalar_finish_at" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRank_fields" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRank_run_at" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttModeSuffix_call_at" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttColsRank_call_at" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttHeaderDispatch_call_at" "NLA.Proofs.TR04.MachineTTInitializationTrace" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverse_naturals" "NLA.Proofs.TR04.MachineTTReverseScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverse_reals" "NLA.Proofs.TR04.MachineTTReverseScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_286" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_287" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_288" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_289" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_290" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_291" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_292" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_293" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_294" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_295" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_296" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_297" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_298" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_299" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_300" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_301" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_302" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_303" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_304" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_305" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_306" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_307" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_308" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_309" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_310" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_311" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_312" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_313" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_314" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_315" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_316" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_317" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_318" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_319" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_320" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_321" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_322" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_323" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_324" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_325" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_326" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_327" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_328" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_329" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_330" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_331" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_332" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_333" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_334" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_335" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_336" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_337" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_338" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_339" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_340" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_341" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_342" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_343" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_344" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_345" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_346" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_347" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_reverse_348" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseReadLabel" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseReadHandler" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseReadAddress" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseReadNatural" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseReadEntry" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseRead_steps" "NLA.Proofs.TR04.MachineTTReverseScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_labels" "NLA.Proofs.TR04.MachineTTReverseLift" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_naturals" "NLA.Proofs.TR04.MachineTTReverseLift" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftDataState" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLift_data_steps" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetupCells" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetupNaturalPrefix" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetupMiddle" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetupEnd" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLift_setup_six" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_setup_twelve" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_setup_eighteen" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_setup_jump" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_setup_steps" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftReturnEnd" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLift_return_steps" "NLA.Proofs.TR04.MachineTTReverseLift" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftCall_naturals" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "private" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseLiftRegisters" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetup_relates" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseLiftSetupStable" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetup_natural_outside" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetup_tag" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftSetup_fields" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverse_lift_at" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseReturnStable" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseLiftReturnEnd_natural" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLiftReturnEnd_fields" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseLift_return_at" "NLA.Proofs.TR04.MachineTTReverseLiftCall" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseRead_naturals" "NLA.Proofs.TR04.MachineTTReverseRead" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseRead_reals" "NLA.Proofs.TR04.MachineTTReverseRead" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseHeader_real_map" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseHeader_natural_map" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseHeaderEnd" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseHeader_real_outside" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseHeader_full_at" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseRead_relates" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseReadEnd" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseRead_call_at" "NLA.Proofs.TR04.MachineTTReverseRead" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseMetadata_naturals" "NLA.Proofs.TR04.MachineTTReverseMetadata" "private" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseMetadata" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttReverseReadEnd_fields" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseMetadataEnd" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseMetadataTime" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseMetadataTime_eq" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseMetadata_run_at" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseMetadataStable" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseMetadataEnd_natural" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseMetadataEnd_real" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseMetadataEnd_fields" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseStartState" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttReverseStart_step" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverse_start_at" "NLA.Proofs.TR04.MachineTTReverseMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseStable" "NLA.Proofs.TR04.MachineTTReverseResult" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTReverseResult" "NLA.Proofs.TR04.MachineTTReverseResult" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TTReverseResult.currentStored" "NLA.Proofs.TR04.MachineTTReverseResult" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseResult.protected" "NLA.Proofs.TR04.MachineTTReverseResult" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseResult.rebase" "NLA.Proofs.TR04.MachineTTReverseResult" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverse_lift_return_at" "NLA.Proofs.TR04.MachineTTReverseResult" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseRegisters" "NLA.Proofs.TR04.MachineTTReverse" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttReverse_at" "NLA.Proofs.TR04.MachineTTReverse" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverse_unmerge_at" "NLA.Proofs.TR04.MachineTTReverse" "public" "theorem"

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 286 = .decrement (⟨84,by decide⟩ : Fin 128) (⟨287,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_286 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 287 = .mulNat (⟨93,by decide⟩ : Fin 128) (⟨125,by decide⟩ : Fin 128) (⟨84,by decide⟩ : Fin 128) (⟨288,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_287 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 288 = .addNat (⟨93,by decide⟩ : Fin 128) (⟨68,by decide⟩ : Fin 128) (⟨93,by decide⟩ : Fin 128) (⟨289,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_288 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 289 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨290,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_289 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 290 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨291,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_290 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 291 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨292,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_291 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 292 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨293,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_292 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 293 = .natural (⟨97,by decide⟩ : Fin 128) 7 (⟨294,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_293 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 294 = .jump (⟨5,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_294 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 295 = .copyNat (⟨85,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨296,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_295 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 296 = .increment (⟨93,by decide⟩ : Fin 128) (⟨297,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_296 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 297 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨298,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_297 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 298 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨299,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_298 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 299 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨300,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_299 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 300 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨301,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_300 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 301 = .natural (⟨97,by decide⟩ : Fin 128) 8 (⟨302,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_301 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 302 = .jump (⟨5,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_302 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 303 = .copyNat (⟨86,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨304,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_303 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 304 = .increment (⟨93,by decide⟩ : Fin 128) (⟨305,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_304 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 305 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨306,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_305 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 306 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨307,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_306 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 307 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨308,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_307 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 308 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨309,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_308 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 309 = .natural (⟨97,by decide⟩ : Fin 128) 9 (⟨310,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_309 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 310 = .jump (⟨5,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_310 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 311 = .copyNat (⟨87,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨312,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_311 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 312 = .increment (⟨93,by decide⟩ : Fin 128) (⟨313,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_312 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 313 = .read (⟨0,by decide⟩ : Fin 16) (⟨93,by decide⟩ : Fin 128) (⟨314,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_313 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 314 = .copyNat (⟨1,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨315,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_314 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 315 = .natural (⟨2,by decide⟩ : Fin 128) 1 (⟨316,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_315 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 316 = .natural (⟨3,by decide⟩ : Fin 128) 0 (⟨317,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_316 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 317 = .natural (⟨97,by decide⟩ : Fin 128) 10 (⟨318,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_317 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 318 = .jump (⟨5,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_318 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 319 = .copyNat (⟨88,by decide⟩ : Fin 128) (⟨2,by decide⟩ : Fin 128) (⟨320,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_319 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 320 = .mulNat (⟨94,by decide⟩ : Fin 128) (⟨84,by decide⟩ : Fin 128) (⟨66,by decide⟩ : Fin 128) (⟨321,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_320 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 321 = .addNat (⟨94,by decide⟩ : Fin 128) (⟨67,by decide⟩ : Fin 128) (⟨94,by decide⟩ : Fin 128) (⟨322,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_321 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 322 = .copyNat (⟨4,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨323,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_322 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 323 = .copyNat (⟨5,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨324,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_323 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 324 = .copyNat (⟨6,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨325,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_324 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 325 = .copyNat (⟨7,by decide⟩ : Fin 128) (⟨85,by decide⟩ : Fin 128) (⟨326,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_325 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 326 = .copyNat (⟨8,by decide⟩ : Fin 128) (⟨86,by decide⟩ : Fin 128) (⟨327,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_326 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 327 = .copyNat (⟨9,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨328,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_327 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 328 = .copyNat (⟨10,by decide⟩ : Fin 128) (⟨94,by decide⟩ : Fin 128) (⟨329,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_328 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 329 = .copyNat (⟨11,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨330,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_329 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 330 = .copyNat (⟨12,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨331,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_330 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 331 = .copyNat (⟨13,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨332,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_331 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 332 = .copyNat (⟨14,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨333,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_332 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 333 = .copyNat (⟨15,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨334,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_333 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 334 = .copyNat (⟨16,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨335,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_334 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 335 = .copyNat (⟨17,by decide⟩ : Fin 128) (⟨88,by decide⟩ : Fin 128) (⟨336,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_335 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 336 = .copyNat (⟨18,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨337,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_336 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 337 = .copyNat (⟨19,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨338,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_337 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 338 = .copyNat (⟨20,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨339,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_338 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 339 = .natural (⟨97,by decide⟩ : Fin 128) 2 (⟨340,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_339 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 340 = .jump (⟨11,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_340 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 341 = .copyNat (⟨123,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨342,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_341 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 342 = .copyNat (⟨89,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨343,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_342 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 343 = .copyNat (⟨90,by decide⟩ : Fin 128) (⟨123,by decide⟩ : Fin 128) (⟨344,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_343 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 344 = .equalNat (⟨84,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨347,by decide⟩ : Fin 512) (⟨345,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_344 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 345 = .decrement (⟨84,by decide⟩ : Fin 128) (⟨346,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_345 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 346 = .jump (⟨287,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_346 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 347 = .mulNat (⟨123,by decide⟩ : Fin 128) (⟨76,by decide⟩ : Fin 128) (⟨64,by decide⟩ : Fin 128) (⟨348,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_347 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example : ttProgram.code 348 = .addNat (⟨123,by decide⟩ : Fin 128) (⟨71,by decide⟩ : Fin 128) (⟨123,by decide⟩ : Fin 128) (⟨349,by decide⟩ : Fin 512) := by
  exact @NLA.Proofs.TR04.ttProgram_code_reverse_348 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (k : Fin 4)
    (hl : s.label=ttReverseReadLabel k) (hs : s.status=.running) (hfour : s.natural 125=4) :
    (ordinaryStep ttProgram)^[8] s=ttReverseReadEntry s k := by
  exact @NLA.Proofs.TR04.ttReverseRead_steps s k hl hs hfour
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (hl : s.label=319) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[3] s=ttReverseLiftDataState s := by
  exact @NLA.Proofs.TR04.ttReverseLift_data_steps s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (hl : s.label=322) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[6] s=ttReverseLiftSetupMiddle s 6 328 (by decide) := by
  exact @NLA.Proofs.TR04.ttReverseLift_setup_six s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttReverseLiftSetupMiddle s 6 328 (by decide))=
      ttReverseLiftSetupMiddle s 12 334 (by decide) := by
  exact @NLA.Proofs.TR04.ttReverseLift_setup_twelve s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttReverseLiftSetupMiddle s 12 334 (by decide))=
      ttReverseLiftSetupMiddle s 18 340 (by decide) := by
  exact @NLA.Proofs.TR04.ttReverseLift_setup_eighteen s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    ordinaryStep ttProgram (ttReverseLiftSetupMiddle s 18 340 (by decide))=
      ttReverseLiftSetupMiddle s 18 11 (by decide) := by
  exact @NLA.Proofs.TR04.ttReverseLift_setup_jump s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (hl : s.label=319) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[22] s=ttReverseLiftSetupEnd s := by
  exact @NLA.Proofs.TR04.ttReverseLift_setup_steps s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (hl : s.label=32) (hs : s.status=.running)
    (htag : s.natural 97=2) (hz : s.natural 127=0) (ho : s.natural 126=1) :
    (ordinaryStep ttProgram)^[8] s=ttReverseLiftReturnEnd s := by
  exact @NLA.Proofs.TR04.ttReverseLift_return_steps s hl hs htag hz ho
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hr : TTReverseLiftRegisters s m q (suffixSize ns) stride frame input output) :
    ttMatrixEmbedding.Relates (matrixMultiplyRowState
      (liftMultiplyData s.memory m q ns frame stride input output) 0 (ttForwardScratch s))
      (ttReverseLiftSetupEnd s) := by
  exact @NLA.Proofs.TR04.ttReverseLiftSetup_relates s m q ns stride frame input output hr
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (i : Fin 128)
    (hi : TTReverseLiftSetupStable i) : (ttReverseLiftSetupEnd s).natural i=s.natural i := by
  exact @NLA.Proofs.TR04.ttReverseLiftSetup_natural_outside s i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    (ttReverseLiftSetupEnd s).natural 97=2 := by
  exact @NLA.Proofs.TR04.ttReverseLiftSetup_tag s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    (ttReverseLiftSetupEnd s).natural 88=s.natural 2 ∧
    (ttReverseLiftSetupEnd s).natural 94=s.natural 67+s.natural 84*s.natural 66 := by
  exact @NLA.Proofs.TR04.ttReverseLiftSetup_fields s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=319) (hs : (trace.state offset).status=.running)
    (hr : TTReverseLiftRegisters (trace.state offset) m q (suffixSize ns) stride frame input output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (q::ns)) (hA : StoresTensor (trace.state offset).memory input (q::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize ns))
    (hAblock : DisjointBlocks input (q*suffixSize ns) output (m*suffixSize ns)) :
    let p := liftMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+22+matrixMultiplyReturnTime p
    (trace.state time).label=32 ∧ (trace.state time).status=.running ∧
    StoresTensor (trace.state time).memory output (m::ns) (lift Q A) ∧
    StoresTensor (trace.state time).memory input (q::ns) A ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, ¬(output≤a ∧ a<output+m*suffixSize ns) →
      (trace.state time).memory a=(trace.state offset).memory a) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+22+17*(m+q+suffixSize ns+1)^3 ∧
    (∀ i : Fin 16, ((i.val < 2) ∨ (5 ≤ i.val)) → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, TTReverseLiftSetupStable i →
      (trace.state time).natural i=(trace.state offset).natural i) ∧
    (trace.state time).natural 97=2 ∧
    (trace.state time).natural 88=stride ∧ (trace.state time).natural 94=frame := by
  exact @NLA.Proofs.TR04.ttReverse_lift_at start trace ht offset m q ns stride frame input output hl hs hr hq Q hQ A hA hQblock hAblock
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) (i : Fin 128)
    (hi : TTReverseReturnStable i) : (ttReverseLiftReturnEnd s).natural i=s.natural i := by
  exact @NLA.Proofs.TR04.ttReverseLiftReturnEnd_natural s i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example (s : State ttProgram) :
    (ttReverseLiftReturnEnd s).label=(if s.natural 84=0 then 349 else 287) ∧
    (ttReverseLiftReturnEnd s).status=.running ∧
    (ttReverseLiftReturnEnd s).natural 89=s.natural 90 ∧
    (ttReverseLiftReturnEnd s).natural 90=s.natural 89 ∧
    (ttReverseLiftReturnEnd s).natural 84=s.natural 84-1 ∧
    (ttReverseLiftReturnEnd s).memory=s.memory ∧ (ttReverseLiftReturnEnd s).real=s.real ∧
    (s.natural 84=0 → (ttReverseLiftReturnEnd s).natural 123=s.natural 71+s.natural 76*s.natural 64) := by
  exact @NLA.Proofs.TR04.ttReverseLiftReturnEnd_fields s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=32) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=2) (hz : (trace.state offset).natural 127=0)
    (ho : (trace.state offset).natural 126=1) :
    trace.state (offset+8)=ttReverseLiftReturnEnd (trace.state offset) ∧
    CostThrough ttProgram trace (offset+8)≤CostThrough ttProgram trace offset+8 := by
  exact @NLA.Proofs.TR04.ttReverseLift_return_at start trace ht offset hl hs htag hz ho
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (i : Fin 2) :
    ttHeaderEmbedding.reals i=(⟨i.val,by have := i.isLt;omega⟩ : Fin 16) := by
  exact @NLA.Proofs.TR04.ttReverseHeader_real_map i
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (i : Fin 4) :
    ttHeaderEmbedding.naturals i=(⟨i.val,by have := i.isLt;omega⟩ : Fin 128) := by
  exact @NLA.Proofs.TR04.ttReverseHeader_natural_map i
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (memory : ℕ → ℝ)
    (d value : ℕ) (scratch : ℝ)
    (he : ttHeaderEmbedding.Relates
      (headerProductDecodeState memory d d 1 value scratch) (trace.state offset))
    (i : Fin 16) (hi : 2 ≤ i.val) :
    (trace.state (offset+(3*value+5))).real i=(trace.state offset).real i := by
  exact @NLA.Proofs.TR04.ttReverseHeader_real_outside start trace ht offset memory d value scratch he i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (memory : ℕ → ℝ)
    (d value : ℕ) (scratch : ℝ)
    (he : ttHeaderEmbedding.Relates
      (headerProductDecodeState memory d d 1 value scratch) (trace.state offset)) :
    trace.state (offset+(3*value+5))=ttReverseHeaderEnd (trace.state offset) d value ∧
    CostThrough ttProgram trace (offset+(3*value+5))≤CostThrough ttProgram trace offset+(3*value+5) := by
  exact @NLA.Proofs.TR04.ttReverseHeader_full_at start trace ht offset memory d value scratch he
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (k : Fin 4) (value : ℕ)
    (hm : s.memory (ttReverseReadAddress s k)=(value : ℝ)) :
    ttHeaderEmbedding.Relates (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value
      (s.real (1 : Fin 16))) (ttReverseReadEntry s k) := by
  exact @NLA.Proofs.TR04.ttReverseRead_relates s k value hm
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 4) (value : ℕ)
    (hl : (trace.state offset).label=ttReverseReadLabel k) (hs : (trace.state offset).status=.running)
    (hfour : (trace.state offset).natural 125=4)
    (hm : (trace.state offset).memory (ttReverseReadAddress (trace.state offset) k)=(value : ℝ)) :
    let time := offset+8+(3*value+5)+(2*(7+k.val)+3)
    trace.state time=ttReverseReadEnd (trace.state offset) k value ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+8+(3*value+5)+(2*(7+k.val)+3) := by
  exact @NLA.Proofs.TR04.ttReverseRead_call_at start trace ht offset k value hl hs hfour hm
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (k : Fin 4) (value : ℕ) :
    (ttReverseReadEnd s k value).label=ttReverseReadHandler k ∧
    (ttReverseReadEnd s k value).status=.running ∧
    (ttReverseReadEnd s k value).memory=s.memory ∧
    (ttReverseReadEnd s k value).natural 2=value ∧
    (ttReverseReadEnd s k value).natural 93=ttReverseReadAddress s k ∧
    (ttReverseReadEnd s k value).natural 125=s.natural 125 := by
  exact @NLA.Proofs.TR04.ttReverseReadEnd_fields s k value
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (m q cols stride : ℕ) :
    ttReverseMetadataTime m q cols stride=3*(m+q+cols+stride)+132 := by
  exact @NLA.Proofs.TR04.ttReverseMetadataTime_eq m q cols stride
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q cols stride : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hfour : (trace.state offset).natural 125=4)
    (hm : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q cols stride) :
    trace.state (offset+ttReverseMetadataTime m q cols stride)=
      ttReverseMetadataEnd (trace.state offset) m q cols stride ∧
    CostThrough ttProgram trace (offset+ttReverseMetadataTime m q cols stride)≤
      CostThrough ttProgram trace offset+ttReverseMetadataTime m q cols stride := by
  exact @NLA.Proofs.TR04.ttReverseMetadata_run_at start trace ht offset m q cols stride hl hs hfour hm
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (m q cols stride : ℕ)
    (i : Fin 128) (hi : TTReverseMetadataStable i) :
    (ttReverseMetadataEnd s m q cols stride).natural i=s.natural i := by
  exact @NLA.Proofs.TR04.ttReverseMetadataEnd_natural s m q cols stride i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (m q cols stride : ℕ)
    (i : Fin 16) (hi : 2 ≤ i.val) :
    (ttReverseMetadataEnd s m q cols stride).real i=s.real i := by
  exact @NLA.Proofs.TR04.ttReverseMetadataEnd_real s m q cols stride i hi
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (m q cols stride : ℕ) :
    (ttReverseMetadataEnd s m q cols stride).label=319 ∧
    (ttReverseMetadataEnd s m q cols stride).status=.running ∧
    (ttReverseMetadataEnd s m q cols stride).memory=s.memory ∧
    (ttReverseMetadataEnd s m q cols stride).natural 85=m ∧
    (ttReverseMetadataEnd s m q cols stride).natural 86=q ∧
    (ttReverseMetadataEnd s m q cols stride).natural 87=cols ∧
    (ttReverseMetadataEnd s m q cols stride).natural 2=stride ∧
    (ttReverseMetadataEnd s m q cols stride).natural 93=s.natural 68+4*s.natural 84+3 := by
  exact @NLA.Proofs.TR04.ttReverseMetadataEnd_fields s m q cols stride
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (hl : s.label=286) (hs : s.status=.running) :
    ordinaryStep ttProgram s=ttReverseStartState s := by
  exact @NLA.Proofs.TR04.ttReverseStart_step s hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=286) (hs : (trace.state offset).status=.running) :
    trace.state (offset+1)=ttReverseStartState (trace.state offset) ∧
    CostThrough ttProgram trace (offset+1)≤CostThrough ttProgram trace offset+1 := by
  exact @NLA.Proofs.TR04.ttReverse_start_at start trace ht offset hl hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A) :
    StoresTensor final.memory (final.natural 89) (m::ns) (lift Q A) := by
  exact @NLA.Proofs.TR04.TTReverseResult.currentStored old final m q ns stride frame input output Q A h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A)
    (base count : ℕ) (hd : DisjointBlocks base count output (m*suffixSize ns)) :
    ∀ a, base≤a ∧ a<base+count → final.memory a=old.memory a := by
  exact @NLA.Proofs.TR04.TTReverseResult.protected old final m q ns stride frame input output Q A h base count hd
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {old mid final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult mid final m q ns stride frame input output Q A)
    (hm : mid.memory=old.memory) (hl : mid.natural 84=old.natural 84)
    (hr : ∀ i : Fin 16,5 ≤ i.val → mid.real i=old.real i)
    (hn : ∀ i : Fin 128,TTReverseStable i → mid.natural i=old.natural i) :
    TTReverseResult old final m q ns stride frame input output Q A := by
  exact @NLA.Proofs.TR04.TTReverseResult.rebase old mid final m q ns stride frame input output Q A h hm hl hr hn
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=319) (hs : (trace.state offset).status=.running)
    (hr : TTReverseLiftRegisters (trace.state offset) m q (suffixSize ns) stride frame input output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (q::ns)) (hA : StoresTensor (trace.state offset).memory input (q::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize ns))
    (hAblock : DisjointBlocks input (q*suffixSize ns) output (m*suffixSize ns)) :
    let p := liftMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+22+matrixMultiplyReturnTime p+8
    TTReverseResult (trace.state offset) (trace.state time) m q ns stride frame input output Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+22+17*(m+q+suffixSize ns+1)^3+8 := by
  exact @NLA.Proofs.TR04.ttReverse_lift_return_at start trace ht offset m q ns stride frame input output hl hs hr hq Q hQ A hA hQblock hAblock
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hr : TTReverseRegisters (trace.state offset) frame input output)
    (hmetadata : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q (suffixSize ns) stride)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (q::ns)) (hA : StoresTensor (trace.state offset).memory input (q::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize ns))
    (hAblock : DisjointBlocks input (q*suffixSize ns) output (m*suffixSize ns)) :
    let p := liftMultiplyData (trace.state offset).memory m q ns frame stride input output
    let metadataTime := ttReverseMetadataTime m q (suffixSize ns) stride
    let time := offset+metadataTime+22+matrixMultiplyReturnTime p+8
    TTReverseResult (trace.state offset) (trace.state time) m q ns stride frame input output Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+metadataTime+22+
      17*(m+q+suffixSize ns+1)^3+8 := by
  exact @NLA.Proofs.TR04.ttReverse_at start trace ht offset m q ns stride frame input output hl hs hr hmetadata hq Q hQ A hA hQblock hAblock
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q n : ℕ) (ns : List ℕ)
    (stride frame input output : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hr : TTReverseRegisters (trace.state offset) frame input output)
    (hmetadata : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q (suffixSize (n::ns)) stride)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (Z : Tensor ((q*n)::ns)) (hZ : StoresTensor (trace.state offset).memory input ((q*n)::ns) Z)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize (n::ns)))
    (hZblock : DisjointBlocks input (q*suffixSize (n::ns)) output (m*suffixSize (n::ns))) :
    let p := liftMultiplyData (trace.state offset).memory m q (n::ns) frame stride input output
    let metadataTime := ttReverseMetadataTime m q (suffixSize (n::ns)) stride
    let time := offset+metadataTime+22+matrixMultiplyReturnTime p+8
    TTReverseResult (trace.state offset) (trace.state time) m q (n::ns) stride frame input output Q
      ((merge q n ns).symm Z) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+metadataTime+22+
      17*(m+q+suffixSize (n::ns)+1)^3+8 := by
  exact @NLA.Proofs.TR04.ttReverse_unmerge_at start trace ht offset m q n ns stride frame input output hl hs hr hmetadata hq Q hQ Z hZ hQblock hZblock
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

-- Actual four-cell metadata decoding, strided lift and buffer swap reach349
-- at the top reverse level, with the destination pointer already computed.
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q : ℕ) (ns : List ℕ)
    (stride frame input output : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hr : TTReverseRegisters (trace.state offset) frame input output)
    (hzero : (trace.state offset).natural 84=0)
    (hmetadata : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q (suffixSize ns) stride)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (q::ns)) (hA : StoresTensor (trace.state offset).memory input (q::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize ns))
    (hAblock : DisjointBlocks input (q*suffixSize ns) output (m*suffixSize ns)) :
    ∃ time : ℕ,(trace.state time).label=349 ∧ (trace.state time).status=.running ∧
      (trace.state time).natural 123=(trace.state offset).natural 71+
        (trace.state offset).natural 76*(trace.state offset).natural 64 ∧
      StoresTensor (trace.state time).memory ((trace.state time).natural 89) (m::ns) (lift Q A) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+
        ttReverseMetadataTime m q (suffixSize ns) stride+22+17*(m+q+suffixSize ns+1)^3+8 := by
  obtain ⟨hresult,hcost⟩ := ttReverse_at ht offset m q ns stride frame input output hl hs hr
    hmetadata hq Q hQ A hA hQblock hAblock
  refine ⟨_,?_,hresult.running,hresult.candidatePointer hzero,hresult.currentStored,hcost⟩
  exact hresult.label.trans (if_pos hzero)

-- For a genuine parent level the same actual return goes to287 and decreases
-- the level, rather than using the top-level candidate-copy continuation.
example {old final : State ttProgram} {m q : ℕ} {ns : List ℕ}
    {stride frame input output : ℕ} {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A)
    (hpositive : 0<old.natural 84) :
    final.label=287 ∧ final.status=.running ∧ final.natural 84+1=old.natural 84 ∧
      StoresTensor final.memory (final.natural 89) (m::ns) (lift Q A) := by
  refine ⟨?_,h.running,?_,h.currentStored⟩
  · simpa only [if_neg (Nat.ne_of_gt hpositive)] using h.label
  · have hh := h.level
    omega

end NLA.Proofs.TR04

end
