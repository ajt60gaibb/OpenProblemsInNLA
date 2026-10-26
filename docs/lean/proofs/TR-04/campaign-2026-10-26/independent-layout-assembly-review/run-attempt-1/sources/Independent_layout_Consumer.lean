import NLA.Proofs.TR04.TTMemoryLayoutMatrix

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
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout "inductive"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.ofShape "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.input "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.input
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.input
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.childV "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childV
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childV
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frames "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frames
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frames
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workA "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workB "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.store "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.store
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Fits "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.fits_same "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.fits_same
#print axioms NLA.Proofs.TR04.TTMemoryLayout.fits_same
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.fits_trans "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.fits_trans
#print axioms NLA.Proofs.TR04.TTMemoryLayout.fits_trans
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.disjoint_symm "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.disjoint_symm
#print axioms NLA.Proofs.TR04.TTMemoryLayout.disjoint_symm
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.disjoint_of_end_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.disjoint_of_end_le
#print axioms NLA.Proofs.TR04.TTMemoryLayout.disjoint_of_end_le
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.disjoint_fits "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.disjoint_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.disjoint_fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.fits_address "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.fits_address
#print axioms NLA.Proofs.TR04.TTMemoryLayout.fits_address
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.square_capacity "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.square_capacity
#print axioms NLA.Proofs.TR04.TTMemoryLayout.square_capacity
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.rectangle_capacity "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.rectangle_capacity
#print axioms NLA.Proofs.TR04.TTMemoryLayout.rectangle_capacity
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_metadata "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_metadata
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_metadata
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_mem "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_mem
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_mem
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_fits "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.header_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.header_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.header_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.input_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.input_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.input_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.input_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.input_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.input_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.childV_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childV_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childV_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_workA "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_workA
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.before_work_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.before_work_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.before_work_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.work_buffers_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.work_buffers_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.work_buffers_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_candidate_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_candidate_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_candidate_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_candidate_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_candidate_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_candidate_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_metadata_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_metadata_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_metadata_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_work_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_work_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_work_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_rectangle_fits "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_rectangle_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_rectangle_fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_rectangle_fits "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_rectangle_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_rectangle_fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_rectangle_fits "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_rectangle_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_rectangle_fits
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.writeSVD_preserves_disjoint_block "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.writeSVD_preserves_disjoint_block
#print axioms NLA.Proofs.TR04.TTMemoryLayout.writeSVD_preserves_disjoint_block
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_frame_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_frame_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_frame_disjoint
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.store_le_endAddress "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.store_le_endAddress
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.store_le_endAddress
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_before_store "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_before_store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_before_store
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_before_store "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_before_store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_before_store
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_before_store "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_before_store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_before_store
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.prefix_address_lt_end "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.prefix_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.prefix_address_lt_end
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_address_lt_end "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_address_lt_end
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_address_lt_end "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_address_lt_end
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_address_lt_end "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_address_lt_end
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_le_cubic "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_le_cubic
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_le_cubic
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.ofShape_input "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape_input
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape_input
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.StageMetadata "inductive"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.Bounded "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.Bounded
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.Bounded
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value_le
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value_le
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.frame_capacity "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.frame_capacity
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.frame_capacity
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.original_value_le_size "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.original_value_le_size
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.original_value_le_size
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
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting "definition"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_inputsOutsideOutput "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_inputsOutsideOutput
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_inputsOutsideOutput
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_inputsOutsideOutput "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_inputsOutsideOutput
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_inputsOutsideOutput
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_leftMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_leftMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_leftMatrix
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_rightMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_rightMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_rightMatrix
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_leftMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_leftMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_leftMatrix
#assert_kind NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_rightMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_rightMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_rightMatrix

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (L : Layout) (level : ℕ) (hl : level < L.order) :
    Fits (L.frame level) (L.entries ^ 2) L.frames (L.order * L.entries ^ 2) := @NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits L level hl
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (L : Layout) (i j : ℕ) (h : i ≠ j) :
    DisjointBlocks (L.frame i) (L.entries ^ 2) (L.frame j) (L.entries ^ 2) := @NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint L i j h
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (L : Layout) (i j f g : ℕ)
    (hf : f < 4) (hg : g < 4)
    (h : L.metadataCell i f = L.metadataCell j g) : i = j ∧ f = g := @NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective L i j f g hf hg h
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (L : Layout) (i j : ℕ) (h : i ≠ j) :
    DisjointBlocks (L.candidate i) L.entries (L.candidate j) L.entries := @NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint L i j h
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (m l : ℕ)
    (hm : m ≤ L.entries) (hl : l ≤ L.entries) :
    OutputBlocksDisjoint m l L.firstU L.firstSigma L.firstV := @NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint L m l hm hl
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level m l : ℕ)
    (hm : m ≤ L.entries) (hl : l ≤ L.entries) :
    OutputBlocksDisjoint m l (L.frame level) L.childSigma L.childV := @NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint L level m l hm hl
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level m q a b : ℕ)
    (hlevel : level < L.order) (hm : m ≤ L.entries) (hq : q ≤ L.entries)
    (hab : a * b ≤ L.entries) :
    DisjointBlocks (L.frame level) (m * q) L.workA (a * b) := @NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint L level m q a b hlevel hm hq hab
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (m l a b : ℕ)
    (hml : m * l ≤ L.entries) (hab : a * b ≤ L.entries) :
    DisjointBlocks L.workA (m * l) L.workB (a * b) := @NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint L m l a b hml hab
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) {m l : ℕ} (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (address : ℕ) (ha : address < L.firstU) :
    writeSVD memory L.firstU L.firstSigma L.firstV U sigma V address = memory address := @NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix L m l memory U sigma V address ha
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level : ℕ) (hlevel : level < L.order)
    {m l : ℕ} (memory : ℕ → ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (hm : m ≤ L.entries) (hl : l ≤ L.entries)
    (address : ℕ) (ha : L.workA ≤ address) :
    writeSVD memory (L.frame level) L.childSigma L.childV U sigma V address = memory address := @NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work L level hlevel m l memory U sigma V hm hl address ha
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) {m l : ℕ} (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (hm : m ≤ L.entries) (hl : l ≤ L.entries)
    (address : ℕ) (ha : L.childSigma ≤ address) :
    writeSVD memory L.firstU L.firstSigma L.firstV U sigma V address = memory address := @NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later L m l memory U sigma V hm hl address ha
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level other : ℕ)
    (hne : level ≠ other) {m l : ℕ} (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (hm : m ≤ L.entries) (hl : l ≤ L.entries)
    (address : ℕ)
    (ha : L.frame other ≤ address ∧ address < L.frame other + L.entries ^ 2) :
    writeSVD memory (L.frame level) L.childSigma L.childV U sigma V address = memory address := @NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame L level other hne m l memory U sigma V hm hl address ha
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (L : Layout) (count : ℕ) :
    L.endAddress count = L.input + (L.order + 3) * L.entries ^ 2 +
      (count + 5) * L.entries + 4 * L.order := @NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq L count
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (count : ℕ)
    (hk : count ≤ DenseSize S + 1) :
    (ofShape S).endAddress count ≤ 20 * (Size S r + 1) ^ 3 := @NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size S r count hk
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (count address : ℕ)
    (hk : count ≤ DenseSize S + 1) (ha : address < (ofShape S).endAddress count) :
    address < 20 * (Size S r + 1) ^ 3 := @NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size S r count address hk ha
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) (hlevel : level < L.order)
    (hm : rows ≤ L.entries) (hq : width ≤ L.entries)
    (hinput : rows * cols ≤ L.entries) (houtput : width * cols ≤ L.entries) :
    (L.contraction level rows width cols memory).InputsOutsideOutput := @NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_inputsOutsideOutput L level rows width cols memory hlevel hm hq hinput houtput
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) (hlevel : level < L.order)
    (hm : rows ≤ L.entries) (hq : width ≤ L.entries)
    (hinput : width * cols ≤ L.entries) (houtput : rows * cols ≤ L.entries) :
    (L.lifting level rows width cols memory).InputsOutsideOutput := @NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_inputsOutsideOutput L level rows width cols memory hlevel hm hq hinput houtput
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) :
    (L.contraction level rows width cols memory).leftMatrix =
      (readMatrix memory rows width (L.frame level)).transpose := @NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_leftMatrix L level rows width cols memory
end NLA.Proofs.TR04.TTMemoryLayout
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
example (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) :
    (L.lifting level rows width cols memory).leftMatrix =
      readMatrix memory rows width (L.frame level) := @NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_leftMatrix L level rows width cols memory
end NLA.Proofs.TR04.TTMemoryLayout

namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

-- Expand the actual heap endpoint in the original input size, preserving K<=N+1.
example (S : Shape) (r : Ranks S) (count : ℕ) (hk : count ≤ DenseSize S + 1) :
    (2 * S.order - 1) + (S.order + 3) * DenseSize S ^ 2 +
      (count + 5) * DenseSize S + 4 * S.order ≤ 20 * (Size S r + 1) ^ 3 := by
  have h := ofShape_endAddress_le_size S r count hk
  rw [Layout.endAddress_eq] at h
  exact h

-- Empty SVD dimensions obey the actual model's disjoint-block convention.
example (L : Layout) : OutputBlocksDisjoint 0 0 L.firstU L.firstSigma L.firstV :=
  L.first_outputs_disjoint 0 0 (Nat.zero_le _) (Nat.zero_le _)

end NLA.Proofs.TR04.TTMemoryLayout

end
