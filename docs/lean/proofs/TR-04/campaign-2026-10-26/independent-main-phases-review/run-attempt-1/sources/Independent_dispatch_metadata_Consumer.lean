import NLA.Proofs.TR04.MachineTTMetadata

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
#audit_named "NLA.Proofs.TR04.ttMetadata_nonzero_realRegisters" "NLA.Proofs.TR04.MachineTTMetadata" "local" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_241" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_242" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_243" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_244" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_245" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_246" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_247" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_248" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_249" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_250" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_251" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_252" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_253" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttProgram_code_metadata_254" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadataCell" "NLA.Proofs.TR04.MachineTTMetadata" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMetadataState" "NLA.Proofs.TR04.MachineTTMetadata" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttMetadata_setup" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_cell_steps" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_cells_prefix" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_steps" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_run_at" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_final_cell" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_fields_at" "NLA.Proofs.TR04.MachineTTMetadata" "public" "theorem"

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (k : Fin 11) :
    ttProgram.code (ttHeaderTagLabel k) = .natural 123 k.val (ttHeaderCompareLabel k) := @NLA.Proofs.TR04.ttProgram_code_header_tag k
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (k : Fin 11) :
    ttProgram.code (ttHeaderCompareLabel k) =
      .equalNat 97 123 (ttHeaderHandler k) (ttHeaderRejectLabel k) := @NLA.Proofs.TR04.ttProgram_code_header_compare k
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (j k : Fin 11)
    (hj : j.val < k.val) (hl : s.label = ttHeaderTagLabel j)
    (hs : s.status = .running) (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2] s = ttHeaderRejectedState s j := @NLA.Proofs.TR04.ttHeader_reject_steps s j k hj hl hs htag
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (k : Fin 11)
    (hl : s.label = ttHeaderTagLabel k) (hs : s.status = .running)
    (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2] s = ttHeaderDispatchEnd s k := @NLA.Proofs.TR04.ttHeader_accept_steps s k hl hs htag
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (remaining : ℕ) (k j : Fin 11)
    (hj : j.val + remaining = k.val) (s : State ttProgram)
    (hl : s.label = ttHeaderTagLabel j) (hs : s.status = .running)
    (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2 * remaining + 2] s = ttHeaderDispatchEnd s k := @NLA.Proofs.TR04.ttHeader_scan_steps remaining k j hj s hl hs htag
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (s : State ttProgram) (k : Fin 11)
    (hl : s.label = 10) (hs : s.status = .running) (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2 * k.val + 3] s = ttHeaderDispatchEnd s k := @NLA.Proofs.TR04.ttHeaderDispatch_steps s k hl hs htag
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {P : Program} (s : State P) (n : ℕ)
    (hn : ((ordinaryStep P)^[n] s).status=.running) (k : ℕ) (hk : k<n) :
    instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label)=false := @NLA.Proofs.TR04.ttOrdinary_nosvd_prefix_of_running P s n hn k hk
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 11)
    (hl : (trace.state offset).label = 10) (hs : (trace.state offset).status = .running)
    (htag : (trace.state offset).natural 97 = k.val) :
    trace.state (offset + (2*k.val+3)) = ttHeaderDispatchEnd (trace.state offset) k ∧
      CostThrough ttProgram trace (offset + (2*k.val+3)) ≤
        CostThrough ttProgram trace offset + (2*k.val+3) := @NLA.Proofs.TR04.ttHeaderDispatch_run_at start trace ht offset k hl hs htag
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 11)
    (hl : (trace.state offset).label = 10) (hs : (trace.state offset).status = .running)
    (htag : (trace.state offset).natural 97 = k.val) :
    let time := offset + (2*k.val+3)
    (trace.state time).label = ttHeaderHandler k ∧
    (trace.state time).status = .running ∧
    (trace.state time).memory = (trace.state offset).memory ∧
    (trace.state time).real = (trace.state offset).real ∧
    (trace.state time).natural 123 = k.val ∧
    (∀ i : Fin 128, i ≠ 123 → (trace.state time).natural i = (trace.state offset).natural i) ∧
    CostThrough ttProgram trace time ≤ CostThrough ttProgram trace offset + (2*k.val+3) := @NLA.Proofs.TR04.ttHeaderDispatch_fields_at start trace ht offset k hl hs htag
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 241 = .mulNat 93 125 84 242 := @NLA.Proofs.TR04.ttProgram_code_metadata_241 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 242 = .addNat 93 68 93 243 := @NLA.Proofs.TR04.ttProgram_code_metadata_242 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 243 = .castNat 13 85 244 := @NLA.Proofs.TR04.ttProgram_code_metadata_243 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 244 = .write 93 13 245 := @NLA.Proofs.TR04.ttProgram_code_metadata_244 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 245 = .increment 93 246 := @NLA.Proofs.TR04.ttProgram_code_metadata_245 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 246 = .castNat 13 86 247 := @NLA.Proofs.TR04.ttProgram_code_metadata_246 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 247 = .write 93 13 248 := @NLA.Proofs.TR04.ttProgram_code_metadata_247 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 248 = .increment 93 249 := @NLA.Proofs.TR04.ttProgram_code_metadata_248 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 249 = .castNat 13 87 250 := @NLA.Proofs.TR04.ttProgram_code_metadata_249 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 250 = .write 93 13 251 := @NLA.Proofs.TR04.ttProgram_code_metadata_250 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 251 = .increment 93 252 := @NLA.Proofs.TR04.ttProgram_code_metadata_251 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 252 = .castNat 13 88 253 := @NLA.Proofs.TR04.ttProgram_code_metadata_252 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 253 = .write 93 13 254 := @NLA.Proofs.TR04.ttProgram_code_metadata_253 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example : ttProgram.code 254 = .increment 93 255 := @NLA.Proofs.TR04.ttProgram_code_metadata_254 
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example (s : State ttProgram) (L : Layout) (level : ℕ)
    (hl : s.label = 241) (hs : s.status = .running)
    (hmeta : s.natural 68 = L.metadata) (hfour : s.natural 125 = 4)
    (hlevel : s.natural 84 = level) :
    (ordinaryStep ttProgram)^[2] s = ttMetadataState s (L.metadata + 4 * level) 0 (by decide) := @NLA.Proofs.TR04.ttMetadata_setup s L level hl hs hmeta hfour hlevel
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example (s : State ttProgram) (base : ℕ) (field : Fin 4) :
    (ordinaryStep ttProgram)^[3] (ttMetadataState s base field.val (by have := field.isLt; omega)) =
      ttMetadataState s base (field.val + 1) (by have := field.isLt; omega) := @NLA.Proofs.TR04.ttMetadata_cell_steps s base field
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example (s : State ttProgram) (base count : ℕ) (hc : count ≤ 4) :
    (ordinaryStep ttProgram)^[3 * count] (ttMetadataState s base 0 (by decide)) =
      ttMetadataState s base count hc := @NLA.Proofs.TR04.ttMetadata_cells_prefix s base count hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example (s : State ttProgram) (L : Layout) (level : ℕ)
    (hl : s.label = 241) (hs : s.status = .running)
    (hmeta : s.natural 68 = L.metadata) (hfour : s.natural 125 = 4)
    (hlevel : s.natural 84 = level) :
    (ordinaryStep ttProgram)^[14] s = ttMetadataState s (L.metadata + 4 * level) 4 (by decide) := @NLA.Proofs.TR04.ttMetadata_steps s L level hl hs hmeta hfour hlevel
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hl : (trace.state offset).label = 241) (hs : (trace.state offset).status = .running)
    (hmeta : (trace.state offset).natural 68 = L.metadata)
    (hfour : (trace.state offset).natural 125 = 4)
    (hlevel : (trace.state offset).natural 84 = level) :
    trace.state (offset + 14) = ttMetadataState (trace.state offset) (L.metadata + 4 * level) 4 (by decide) ∧
      CostThrough ttProgram trace (offset + 14) ≤ CostThrough ttProgram trace offset + 14 := @NLA.Proofs.TR04.ttMetadata_run_at start trace ht offset L level hl hs hmeta hfour hlevel
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example (s : State ttProgram) (base : ℕ) (field : Fin 4) :
    (ttMetadataState s base 4 (by decide)).memory (base + field.val) =
      (s.natural (⟨85 + field.val,by have := field.isLt;omega⟩ : Fin 128) : ℝ) := @NLA.Proofs.TR04.ttMetadata_final_cell s base field
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hl : (trace.state offset).label = 241) (hs : (trace.state offset).status = .running)
    (hmeta : (trace.state offset).natural 68 = L.metadata)
    (hfour : (trace.state offset).natural 125 = 4)
    (hlevel : (trace.state offset).natural 84 = level) :
    (trace.state (offset+14)).label = 255 ∧
    (trace.state (offset+14)).status = .running ∧
    (trace.state (offset+14)).natural 93 = L.metadata+4*level+4 ∧
    (∀ field : Fin 4, (trace.state (offset+14)).memory (L.metadataCell level field.val) =
      ((trace.state offset).natural (⟨85+field.val,by have := field.isLt;omega⟩ : Fin 128) : ℝ)) ∧
    (∀ address, ¬(L.metadata+4*level ≤ address ∧ address < L.metadata+4*level+4) →
      (trace.state (offset+14)).memory address = (trace.state offset).memory address) ∧
    (∀ i : Fin 128, i ≠ 93 → (trace.state (offset+14)).natural i = (trace.state offset).natural i) ∧
    (∀ i : Fin 16, i ≠ 13 → (trace.state (offset+14)).real i = (trace.state offset).real i) ∧
    CostThrough ttProgram trace (offset+14) ≤ CostThrough ttProgram trace offset+14 := @NLA.Proofs.TR04.ttMetadata_fields_at start trace ht offset L level hl hs hmeta hfour hlevel
end NLA.Proofs.TR04

namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout

example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 10) (hs : (trace.state offset).status = .running)
    (htag : (trace.state offset).natural 97 = 0) :
    (trace.state (offset + 3)).label = 119 ∧
    (trace.state (offset + 3)).memory = (trace.state offset).memory ∧
    CostThrough ttProgram trace (offset + 3) ≤ CostThrough ttProgram trace offset + 3 := by
  have h := ttHeaderDispatch_fields_at ht offset 0 hl hs htag
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.2⟩

example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 10) (hs : (trace.state offset).status = .running)
    (htag : (trace.state offset).natural 97 = 10) :
    (trace.state (offset + 23)).label = 319 ∧
    (trace.state (offset + 23)).memory = (trace.state offset).memory ∧
    CostThrough ttProgram trace (offset + 23) ≤ CostThrough ttProgram trace offset + 23 := by
  have h := ttHeaderDispatch_fields_at ht offset 10 hl hs htag
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.2⟩

-- The four stored metadata cells are actual casts of the four old registers.
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hl : (trace.state offset).label = 241) (hs : (trace.state offset).status = .running)
    (hmeta : (trace.state offset).natural 68 = L.metadata)
    (hfour : (trace.state offset).natural 125 = 4)
    (hlevel : (trace.state offset).natural 84 = level) :
    (trace.state (offset + 14)).memory (L.metadataCell level 0) = ((trace.state offset).natural 85 : ℝ) ∧
    (trace.state (offset + 14)).memory (L.metadataCell level 1) = ((trace.state offset).natural 86 : ℝ) ∧
    (trace.state (offset + 14)).memory (L.metadataCell level 2) = ((trace.state offset).natural 87 : ℝ) ∧
    (trace.state (offset + 14)).memory (L.metadataCell level 3) = ((trace.state offset).natural 88 : ℝ) := by
  have h := ttMetadata_fields_at ht offset L level hl hs hmeta hfour hlevel
  exact ⟨h.2.2.2.1 0, h.2.2.2.1 1, h.2.2.2.1 2, h.2.2.2.1 3⟩

end NLA.Proofs.TR04

end
