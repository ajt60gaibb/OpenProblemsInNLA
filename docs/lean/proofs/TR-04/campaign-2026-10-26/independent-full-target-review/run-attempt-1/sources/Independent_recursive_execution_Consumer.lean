import NLA.Proofs.TR04.MachineTTRecursiveChild

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
#audit_named "NLA.Proofs.TR04.TTStageProtected" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTStageWritable" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttStageProtected_mono" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStageProtected_not_writable" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStageProtected_own_frame" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStageProtected_own_metadata" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStageProtected_work_outside" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStageProtected_metadata_outside" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStageProtected_child_svd" "NLA.Proofs.TR04.MachineTTStageProtection" "public" "theorem"
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
#audit_named "NLA.Proofs.TR04.ttChildSVD_naturals" "NLA.Proofs.TR04.MachineTTChildSVD" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildSVD_code238" "NLA.Proofs.TR04.MachineTTChildSVD" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildSVD_code239" "NLA.Proofs.TR04.MachineTTChildSVD" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildSVD_code240" "NLA.Proofs.TR04.MachineTTChildSVD" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildSVDReturnState" "NLA.Proofs.TR04.MachineTTChildSVD" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildSVDReturn_steps" "NLA.Proofs.TR04.MachineTTChildSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_svd_at" "NLA.Proofs.TR04.MachineTTChildSVD" "public" "theorem"
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
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveModes" "NLA.Proofs.TR04.TTDimensionBounds" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveRanks" "NLA.Proofs.TR04.TTDimensionBounds" "public" "definition"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.step_length" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.StepBounds" "NLA.Proofs.TR04.TTDimensionBounds" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product" "NLA.Proofs.TR04.TTDimensionBounds" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix" "NLA.Proofs.TR04.TTDimensionBoundsReachable" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRankValue" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttFirstCols" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "definition"
#audit_named "NLA.Proofs.TR04.inputMemory_rankHeader" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.inputMemory_firstRank" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRangeProduct_shape_drop" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstCols_prod" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstCols_pos" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstCols_le_denseSize" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstMode_le_size" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFirstRankValue_le_size" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.headerRangeTime_shape_le_size" "NLA.Proofs.TR04.MachineTTInitialShape" "public" "theorem"
#audit_named "NLA.Proofs.TR04.code208" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code209" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code210" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code211" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code212" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code213" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code214" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code215" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code216" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code217" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code218" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code219" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code220" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code221" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code222" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code223" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code224" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code225" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code226" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code227" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code228" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code229" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code230" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code231" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code232" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code233" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code234" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code235" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.code236" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "private" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildModeEntry" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildSuffixEntry" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildRankEntry" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildCapRowsEnd" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildCapColsEnd" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildCapEnd" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChild_mode_steps" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_suffix_steps" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_rank_steps" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_cap_rows_steps" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_cap_cols_steps" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_cap_steps" "NLA.Proofs.TR04.MachineTTChildInitializationScalar" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTChildKept" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTChildPreserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttChildPreserves_trans" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_mode_preserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_suffix_preserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_rank_preserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_cap_preserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_dispatch_preserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_header_preserves" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildMode_relates" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildSuffix_relates" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildRank_relates" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_cap_fields" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_cap_at" "NLA.Proofs.TR04.MachineTTChildInitializationHelpers" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTLoopKept" "NLA.Proofs.TR04.MachineTTLoopState" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTStagePreserves" "NLA.Proofs.TR04.MachineTTLoopState" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTWorkPair" "NLA.Proofs.TR04.MachineTTLoopState" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_refl" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_trans" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_lower" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_allocation" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttLoopKept_not_metadataScratch" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttLoopKept_child" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttLoopKept_forward" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildPreserves_stage" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTForwardResult.stagePreserves" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttMetadata_stagePreserves_at" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_prior_frame" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_prior_metadata" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttLoopKept_not_childSvdScratch" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_of_childSvd" "NLA.Proofs.TR04.MachineTTLoopState" "public" "theorem"
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
#audit_named "NLA.Proofs.TR04.TTStageBuffers" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "definition"
#audit_named "NLA.Proofs.TR04.TTWorkPair.current_ge" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTWorkPair.output_choice" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTWorkPair.disjoint" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTStageBuffers.output_choice" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTStageBuffers.input_output_disjoint" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttFrame_output_disjoint" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttLoopKept_reverse" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseResult.stagePreserves" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseResult.workPair" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStagePreserves_header" "NLA.Proofs.TR04.MachineTTRecursiveState" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.next_mode_header" "NLA.Proofs.TR04.TTRecursiveDimensions" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.forward_test_iff" "NLA.Proofs.TR04.TTRecursiveDimensions" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TensorFormat.Dimensions.shifted_rank_succ" "NLA.Proofs.TR04.TTRecursiveDimensions" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTStageData" "NLA.Proofs.TR04.MachineTTStageMetadata" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TTStageData.stride_bounds" "NLA.Proofs.TR04.MachineTTStageMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTStageBuffers.input_choice" "NLA.Proofs.TR04.MachineTTStageMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStage_input_metadata_disjoint" "NLA.Proofs.TR04.MachineTTStageMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStage_frame_metadata_disjoint" "NLA.Proofs.TR04.MachineTTStageMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStage_metadata_at" "NLA.Proofs.TR04.MachineTTStageMetadata" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTReverseMetadata.memory_eq" "NLA.Proofs.TR04.MachineTTStageForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTStageForwardResult" "NLA.Proofs.TR04.MachineTTStageForward" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttStageForward_pack" "NLA.Proofs.TR04.MachineTTStageForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStage_forward_at" "NLA.Proofs.TR04.MachineTTStageForward" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_svd_stage_at" "NLA.Proofs.TR04.MachineTTStageChildSVD" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttRecursiveUnit" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "definition"
#audit_named "NLA.Proofs.TR04.ttRecursiveUnit_pos" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttRecursiveUnit_linear" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttRecursive_cube_three" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttRecursive_cube_two" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttRecursive_own_stage_budget" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttRecursive_prefix_budget" "NLA.Proofs.TR04.TTRecursiveBudget" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTCoreResult" "NLA.Proofs.TR04.MachineTTRecursiveResult" "public" "inductive"
#audit_named "NLA.Proofs.TR04.TTCoreResult.prefixCompletion" "NLA.Proofs.TR04.MachineTTRecursiveResult" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttLoopKept_not_level" "NLA.Proofs.TR04.MachineTTStageReverse" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseStart_preserves" "NLA.Proofs.TR04.MachineTTStageReverse" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttReverseStart_workPair" "NLA.Proofs.TR04.MachineTTStageReverse" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttStage_reverse_at" "NLA.Proofs.TR04.MachineTTStageReverse" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttCore_two_at" "NLA.Proofs.TR04.MachineTTRecursiveBase" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_mode_call_at" "NLA.Proofs.TR04.MachineTTChildInitializationCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_suffix_call_at" "NLA.Proofs.TR04.MachineTTChildInitializationCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_rank_call_at" "NLA.Proofs.TR04.MachineTTChildInitializationCalls" "public" "theorem"
#audit_named "NLA.Proofs.TR04.TTChildInitialized" "NLA.Proofs.TR04.MachineTTChildInitialization" "public" "inductive"
#audit_named "NLA.Proofs.TR04.ttChild_initialize_at" "NLA.Proofs.TR04.MachineTTChildInitialization" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChildPreserves_allocation" "NLA.Proofs.TR04.MachineTTChildInitializationOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_mode_le_size" "NLA.Proofs.TR04.MachineTTChildInitializationOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_rank_le_size" "NLA.Proofs.TR04.MachineTTChildInitializationOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_initialize_original_at" "NLA.Proofs.TR04.MachineTTChildInitializationOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_initialize_reachable_at" "NLA.Proofs.TR04.MachineTTChildInitializationOriginal" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttCore_complete_at" "NLA.Proofs.TR04.MachineTTRecursiveExecution" "public" "theorem"
#audit_named "NLA.Proofs.TR04.ttChild_complete_at" "NLA.Proofs.TR04.MachineTTRecursiveChild" "public" "theorem"

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
attribute [local instance] NLA.Proofs.TR04.ttMetadata_nonzero_realRegisters
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (s : State ttProgram) (h : TTWorkPair L s) :
    L.workA≤s.natural 89 := by
  exact @NLA.Proofs.TR04.TTWorkPair.current_ge L s h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (s : State ttProgram) (h : TTWorkPair L s) :
    s.natural 90=L.workA ∨ s.natural 90=L.workB := by
  exact @NLA.Proofs.TR04.TTWorkPair.output_choice L s h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (s : State ttProgram) (h : TTWorkPair L s)
    (a b : ℕ) (ha : a≤L.entries) (hb : b≤L.entries) :
    DisjointBlocks (s.natural 89) a (s.natural 90) b := by
  exact @NLA.Proofs.TR04.TTWorkPair.disjoint L s h a b ha hb
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {L : Layout} {s : State ttProgram} (h : TTStageBuffers L s) :
    s.natural 90=L.workA ∨ s.natural 90=L.workB := by
  exact @NLA.Proofs.TR04.TTStageBuffers.output_choice L s h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {L : Layout} {s : State ttProgram}
    (h : TTStageBuffers L s) (a b : ℕ) (ha : a≤L.entries) (hb : b≤L.entries) :
    DisjointBlocks (s.natural 89) a (s.natural 90) b := by
  exact @NLA.Proofs.TR04.TTStageBuffers.input_output_disjoint L s h a b ha hb
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (level : ℕ) (hl : level<L.order)
    (m stride output count : ℕ) (hm : m≤L.entries) (hs : stride≤L.entries)
    (hout : output=L.workA ∨ output=L.workB) (hc : count≤L.entries) :
    DisjointBlocks (L.frame level) (m*stride) output count := by
  exact @NLA.Proofs.TR04.ttFrame_output_disjoint L level hl m stride output count hm hs hout hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (j : Fin 128) (hj : TTLoopKept j) : TTReverseStable j := by
  exact @NLA.Proofs.TR04.ttLoopKept_reverse j hj
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A)
    (L : Layout) (level : ℕ) (hl : level<L.order)
    (hout : output=L.workA ∨ output=L.workB) (hc : m*suffixSize ns≤L.entries) :
    TTStagePreserves L level old final := by
  exact @NLA.Proofs.TR04.TTReverseResult.stagePreserves old final m q ns stride frame input output Q A h L level hl hout hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {old final : State ttProgram}
    {L : Layout} {m q : ℕ} {ns : List ℕ} {stride frame : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame (old.natural 89) (old.natural 90) Q A)
    (hp : TTWorkPair L old) : TTWorkPair L final := by
  exact @NLA.Proofs.TR04.TTReverseResult.workPair old final L m q ns stride frame Q A h hp
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {L : Layout} {level : ℕ} {s t : State ttProgram}
    (h : TTStagePreserves L level s t) (address : ℕ) (ha : address<L.input) :
    t.memory address=s.memory address := by
  exact @NLA.Proofs.TR04.ttStagePreserves_header L level s t h address ha
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :
    shapeHeaderValues S (level+1)=n := by
  exact @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.next_mode_header S r hr level m n ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :
    (level+1<S.order-1) ↔ ns≠[] := by
  exact @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.forward_test_iff S r hr level m n ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (r : ℕ → ℕ) (level : ℕ) :
    (fun j => r (level+(j+1)))=(fun j => r ((level+1)+j)) := by
  exact @NLA.Proofs.TR04.TensorFormat.Dimensions.shifted_rank_succ r level
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {L : Layout} {level m q : ℕ} {ns : List ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)} {s : State ttProgram}
    (h : TTStageData L level m q ns Q A s) (hqm : q≤m) (hm : m≤L.entries) :
    q≤s.natural 88 ∧ s.natural 88≤L.entries := by
  exact @NLA.Proofs.TR04.TTStageData.stride_bounds L level m q ns Q A s h hqm hm
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {L : Layout} {s : State ttProgram} (h : TTStageBuffers L s) :
    s.natural 89=L.input ∨ s.natural 89=L.workA ∨ s.natural 89=L.workB := by
  exact @NLA.Proofs.TR04.TTStageBuffers.input_choice L s h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (level base count : ℕ)
    (hl : level<L.order) (hb : base=L.input ∨ base=L.workA ∨ base=L.workB)
    (hc : count≤L.entries) : DisjointBlocks base count (L.metadata+4*level) 4 := by
  exact @NLA.Proofs.TR04.ttStage_input_metadata_disjoint L level base count hl hb hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (level m stride : ℕ)
    (hl : level<L.order) (hm : m≤L.entries) (hs : stride≤L.entries) :
    DisjointBlocks (L.frame level) (m*stride) (L.metadata+4*level) 4 := by
  exact @NLA.Proofs.TR04.ttStage_frame_metadata_disjoint L level m stride hl hm hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (level m q : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData L level m q ns Q A (trace.state offset))
    (hlevel : level<L.order) (hqm : q≤m) (hm : m≤L.entries) (hc : m*suffixSize ns≤L.entries) :
    (trace.state (offset+14)).label=255 ∧ (trace.state (offset+14)).status=.running ∧
    TTStageData L level m q ns Q A (trace.state (offset+14)) ∧
    TTReverseMetadata (trace.state (offset+14)).memory (L.metadata+4*level) m q (suffixSize ns)
      ((trace.state offset).natural 88) ∧
    TTStagePreserves L level (trace.state offset) (trace.state (offset+14)) ∧
    (∀ j : Fin 128,j≠93 → (trace.state (offset+14)).natural j=(trace.state offset).natural j) ∧
    CostThrough ttProgram trace (offset+14)≤CostThrough ttProgram trace offset+14 := by
  exact @NLA.Proofs.TR04.ttStage_metadata_at start trace ht offset L level m q ns Q A hl hs hd hlevel hqm hm hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {memory memory' : ℕ → ℝ} {base m q cols stride : ℕ}
    (h : TTReverseMetadata memory base m q cols stride)
    (he : ∀ a,base≤a ∧ a<base+4 → memory' a=memory a) :
    TTReverseMetadata memory' base m q cols stride := by
  exact @NLA.Proofs.TR04.TTReverseMetadata.memory_eq memory memory' base m q cols stride h he
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {old middle final : State ttProgram}
    (L : Layout) (level m q n : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns))
    (hmiddle : TTStageData L level m q (n::ns) Q A middle)
    (hmeta : TTReverseMetadata middle.memory (L.metadata+4*level) m q (suffixSize (n::ns)) (old.natural 88))
    (hpres : TTStagePreserves L level old middle)
    (hlevel : level<L.order) (hcount : q*suffixSize (n::ns)≤L.entries)
    (next : ℕ)
    (h : TTForwardResult middle final m q (n::ns) (old.natural 88) (L.frame level)
      (middle.natural 89) (middle.natural 90) next Q A)
    (hp : TTWorkPair L final) : TTStageForwardResult old final L level m q n ns Q A := by
  exact @NLA.Proofs.TR04.ttStageForward_pack old middle final L level m q n ns Q A hmiddle hmeta hpres hlevel hcount next h hp
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (level m q n : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData L level m q (n::ns) Q A (trace.state offset))
    (hlevel : level<L.order) (hqm : q≤m) (hm : m≤L.entries)
    (hc : m*suffixSize (n::ns)≤L.entries) :
    ∃ elapsed : ℕ,elapsed≤44+17*(m+q+suffixSize (n::ns)+1)^3 ∧
      TTStageForwardResult (trace.state offset) (trace.state (offset+elapsed)) L level m q n ns Q A ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        44+17*(m+q+suffixSize (n::ns)+1)^3 := by
  exact @NLA.Proofs.TR04.ttStage_forward_at start trace ht offset L level m q n ns Q A hl hs hd hlevel hqm hm hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (level m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) (A : Tensor (m::ns))
    (hl : (trace.state offset).label=237) (hs : (trace.state offset).status=.running)
    (ha : TTAllocationRegisters L (trace.state offset))
    (hlevel : (trace.state offset).natural 84=level) (hlevelBound : level<L.order)
    (hrows : (trace.state offset).natural 85=m)
    (hwidth : (trace.state offset).natural 86=stepRank m ns r)
    (hcols : (trace.state offset).natural 87=suffixSize ns)
    (hframe : (trace.state offset).natural 94=L.frame level)
    (hpair : TTWorkPair L (trace.state offset))
    (hA : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) (m::ns) A)
    (hm : m≤L.entries) (hc : suffixSize ns≤L.entries) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
    ∃ sigma : Fin (min m (suffixSize ns)) → ℝ,
    ∃ V : Matrix (Fin (suffixSize ns)) (Fin (suffixSize ns)) ℝ,
      ValidSVD (radixDenseFirst A) U sigma V ∧
      (trace.state (offset+4)).label=241 ∧ (trace.state (offset+4)).status=.running ∧
      TTStageData L level m (stepRank m ns r) ns (stepFrame ns r U) A (trace.state (offset+4)) ∧
      TTStagePreserves L level (trace.state offset) (trace.state (offset+4)) ∧
      CostThrough ttProgram trace (offset+4)≤CostThrough ttProgram trace offset+(m+suffixSize ns+1)^3+3 := by
  exact @NLA.Proofs.TR04.ttChild_svd_stage_at start trace ht offset L level m ns r A hl hs ha hlevel hlevelBound hrows hwidth hcols hframe hpair hA hm hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (size : ℕ) : 0<ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttRecursiveUnit_pos size
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (size : ℕ) : size+1≤ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttRecursiveUnit_linear size
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (size m q cols : ℕ) (hm : m≤size) (hq : q≤size) (hc : cols≤size) :
    (m+q+cols+1)^3≤27*ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttRecursive_cube_three size m q cols hm hq hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (size m cols : ℕ) (hm : m≤size) (hc : cols≤size) :
    (m+cols+1)^3+3≤11*ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttRecursive_cube_two size m cols hm hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (size m q cols stride : ℕ)
    (hm : m≤size) (hq : q≤size) (hc : cols≤size) (hs : stride≤size) :
    (44+17*(m+q+cols+1)^3)+1+(3*(m+q+cols+stride)+132)+22+
      17*(m+q+cols+1)^3+8+100*(size+1)≤2000*ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttRecursive_own_stage_budget size m q cols stride hm hq hc hs
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
example (size depth charge : ℕ)
    (hcharge : charge≤11*ttRecursiveUnit size) :
    charge+(3000*depth*ttRecursiveUnit size+2000*ttRecursiveUnit size)≤
      3000*(depth+1)*ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttRecursive_prefix_budget size depth charge hcharge
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {old final : State ttProgram} {L : Layout}
    {level m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n::ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n::ns))) (Fin (suffixSize (n::ns))) ℝ}
    {A : Tensor (m::n::ns)} {Z : Tensor ((stepRank m (n::ns) r*n)::ns)}
    (h : TTCoreResult old final L level m (stepRank m (n::ns) r) n ns r (stepFrame (n::ns) r U) A Z)
    (hSVD : ValidSVD (radixDenseFirst A) U sigma V) :
    Completion (m::n::ns) r A (stepOutput r U Z) := by
  exact @NLA.Proofs.TR04.TTCoreResult.prefixCompletion old final L level m n ns r U sigma V A Z h hSVD
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (j : Fin 128) (hj : TTLoopKept j) : j≠84 := by
  exact @NLA.Proofs.TR04.ttLoopKept_not_level j hj
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example (L : Layout) (level : ℕ) (s : State ttProgram) :
    TTStagePreserves L level s (ttReverseStartState s) := by
  exact @NLA.Proofs.TR04.ttReverseStart_preserves L level s
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {L : Layout} {s : State ttProgram} (h : TTWorkPair L s) :
    TTWorkPair L (ttReverseStartState s) := by
  exact @NLA.Proofs.TR04.ttReverseStart_workPair L s h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (old : State ttProgram) (forwardTime readTime : ℕ)
    (L : Layout) (level m q n : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns)) (Z : Tensor ((q*n)::ns))
    (hd : TTStageData L level m q (n::ns) Q A old)
    (hf : TTStageForwardResult old (trace.state forwardTime) L level m q n ns Q A)
    (hprotected : TTStagePreserves L (level+1) (trace.state forwardTime) (trace.state readTime))
    (hlabel : (trace.state readTime).label=287) (hrunning : (trace.state readTime).status=.running)
    (hreadLevel : (trace.state readTime).natural 84=level) (hpair : TTWorkPair L (trace.state readTime))
    (hZ : StoresTensor (trace.state readTime).memory ((trace.state readTime).natural 89) ((q*n)::ns) Z)
    (hcompletion : Completion ((q*n)::ns) (fun j => r (j+1)) (merge q n ns (contract Q A)) Z)
    (hlevel : level<L.order) (hqm : q≤m) (hm : m≤L.entries) (hc : m*suffixSize (n::ns)≤L.entries) :
    ∃ elapsed : ℕ,elapsed≤ttReverseMetadataTime m q (suffixSize (n::ns)) (old.natural 88)+30+
        17*(m+q+suffixSize (n::ns)+1)^3 ∧
      TTCoreResult old (trace.state (readTime+elapsed)) L level m q n ns r Q A Z ∧
      CostThrough ttProgram trace (readTime+elapsed)≤CostThrough ttProgram trace readTime+
        ttReverseMetadataTime m q (suffixSize (n::ns)) (old.natural 88)+30+
        17*(m+q+suffixSize (n::ns)+1)^3 := by
  exact @NLA.Proofs.TR04.ttStage_reverse_at start trace ht old forwardTime readTime L level m q n ns r Q A Z hd hf hprotected hlabel hrunning hreadLevel hpair hZ hcompletion hlevel hqm hm hc
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (size level m q n : ℕ) (r : ℕ → ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor [m,n])
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData L level m q [n] Q A (trace.state offset))
    (hlast : level+2=L.order) (hqm : q≤m) (hm : m≤L.entries)
    (hc : m*suffixSize [n]≤L.entries) (hcols : suffixSize [n]≤L.entries) (hsize : L.entries≤size) :
    ∃ elapsed : ℕ,∃ Z : Tensor [q*n],elapsed≤2000*ttRecursiveUnit size ∧
      TTCoreResult (trace.state offset) (trace.state (offset+elapsed)) L level m q n [] r Q A Z ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+2000*ttRecursiveUnit size := by
  exact @NLA.Proofs.TR04.ttCore_two_at start trace ht offset L size level m q n r Q A hl hs hd hlast hqm hm hc hcols hsize
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
open NLA.Computation.TensorTrainApproximation (Shape Ranks DenseSize Size InputMemory)
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace)
    (S : Shape) (r : Ranks S) (A0 : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hr : ∀ j,1≤r j) (ns : List ℕ) (offset level m n : ℕ)
    (Q : Matrix (Fin m) (Fin (stepRank m (n::ns) (fun j => originalRanks S r (level+j)))) ℝ)
    (A : Tensor (m::n::ns))
    (hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData (ofShape S) level m (stepRank m (n::ns) (fun j => originalRanks S r (level+j)))
      (n::ns) Q A (trace.state offset))
    (hheader : ∀ a,a<(ofShape S).input → (trace.state offset).memory a=InputMemory S r A0 a) :
    ∃ elapsed : ℕ,∃ Z : Tensor ((stepRank m (n::ns) (fun j => originalRanks S r (level+j))*n)::ns),
      elapsed≤3000*ns.length*ttRecursiveUnit (Size S r)+2000*ttRecursiveUnit (Size S r) ∧
      TTCoreResult (trace.state offset) (trace.state (offset+elapsed)) (ofShape S) level m
        (stepRank m (n::ns) (fun j => originalRanks S r (level+j))) n ns
        (fun j => originalRanks S r (level+j)) Q A Z ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        (3000*ns.length*ttRecursiveUnit (Size S r)+2000*ttRecursiveUnit (Size S r)) := by
  exact @NLA.Proofs.TR04.ttCore_complete_at start trace ht S r A0 hr ns offset level m n Q A hreach hl hs hd hheader
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
open NLA.Computation.TensorTrainApproximation (Shape Ranks Size InputMemory)
example {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace)
    (S : Shape) (r : Ranks S) (A0 : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hr : ∀ j,1≤r j) (offset level m n : ℕ) (ns : List ℕ) (A : Tensor (m::n::ns))
    (hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns))
    (hl : (trace.state offset).label=237) (hs : (trace.state offset).status=.running)
    (ha : TTAllocationRegisters (ofShape S) (trace.state offset))
    (hlevel : (trace.state offset).natural 84=level)
    (hrows : (trace.state offset).natural 85=m)
    (hwidth : (trace.state offset).natural 86=stepRank m (n::ns) (fun j => originalRanks S r (level+j)))
    (hcols : (trace.state offset).natural 87=suffixSize (n::ns))
    (hframe : (trace.state offset).natural 94=(ofShape S).frame level)
    (hpair : TTWorkPair (ofShape S) (trace.state offset))
    (hA : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) (m::n::ns) A)
    (hheader : ∀ a,a<(ofShape S).input → (trace.state offset).memory a=InputMemory S r A0 a) :
    ∃ elapsed : ℕ,∃ Y : Tensor (m::n::ns),
      elapsed≤3000*(ns.length+1)*ttRecursiveUnit (Size S r) ∧
      Completion (m::n::ns) (fun j => originalRanks S r (level+j)) A Y ∧
      (trace.state (offset+elapsed)).label=(if level=0 then 349 else 287) ∧
      (trace.state (offset+elapsed)).status=.running ∧
      (trace.state (offset+elapsed)).natural 84=level-1 ∧
      StoresTensor (trace.state (offset+elapsed)).memory ((trace.state (offset+elapsed)).natural 89) (m::n::ns) Y ∧
      TTWorkPair (ofShape S) (trace.state (offset+elapsed)) ∧
      TTStagePreserves (ofShape S) level (trace.state offset) (trace.state (offset+elapsed)) ∧
      TTAllocationRegisters (ofShape S) (trace.state (offset+elapsed)) ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        3000*(ns.length+1)*ttRecursiveUnit (Size S r) := by
  exact @NLA.Proofs.TR04.ttChild_complete_at start trace ht S r A0 hr offset level m n ns A hreach hl hs ha hlevel hrows hwidth hcols hframe hpair hA hheader
end NLA.Proofs.TR04
-- Every full literal public type is checked above, including actual recursive
-- core and child execution, stored Completion witnesses and original charges.

end
