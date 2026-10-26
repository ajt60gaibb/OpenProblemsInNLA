import NLA.Proofs.TR04.TTDimensionBoundsReachable

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
#assert_kind NLA.Proofs.TR04.splitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.splitIndex
#print axioms NLA.Proofs.TR04.splitIndex
#assert_kind NLA.Proofs.TR04.splitIndex_join "theorem"
#assert_trust kernel NLA.Proofs.TR04.splitIndex_join
#print axioms NLA.Proofs.TR04.splitIndex_join
#assert_kind NLA.Proofs.TR04.join_splitIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.join_splitIndex
#print axioms NLA.Proofs.TR04.join_splitIndex
#assert_kind NLA.Proofs.TR04.joinEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.joinEquiv
#print axioms NLA.Proofs.TR04.joinEquiv
#assert_kind NLA.Proofs.TR04.unfoldLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.unfoldLinearEquiv
#print axioms NLA.Proofs.TR04.unfoldLinearEquiv
#assert_kind NLA.Proofs.TR04.unfoldContinuousLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.unfoldContinuousLinearEquiv
#print axioms NLA.Proofs.TR04.unfoldContinuousLinearEquiv
#assert_kind NLA.Proofs.TR04.unfoldLinearEquiv_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfoldLinearEquiv_apply
#print axioms NLA.Proofs.TR04.unfoldLinearEquiv_apply
#assert_kind NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply
#print axioms NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply
#assert_kind NLA.Proofs.TR04.continuous_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.continuous_unfold
#print axioms NLA.Proofs.TR04.continuous_unfold
#assert_kind NLA.Proofs.TR04.unfold_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_zero
#print axioms NLA.Proofs.TR04.unfold_zero
#assert_kind NLA.Proofs.TR04.unfold_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_add
#print axioms NLA.Proofs.TR04.unfold_add
#assert_kind NLA.Proofs.TR04.unfold_smul "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_smul
#print axioms NLA.Proofs.TR04.unfold_smul
#assert_kind NLA.Proofs.TR04.unfold_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_injective
#print axioms NLA.Proofs.TR04.unfold_injective
#assert_kind NLA.Proofs.TR04.sum_unfold_indices "theorem"
#assert_trust kernel NLA.Proofs.TR04.sum_unfold_indices
#print axioms NLA.Proofs.TR04.sum_unfold_indices
#assert_kind NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum
#print axioms NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum
#assert_kind NLA.Proofs.TR04.TensorFormat.Index "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Index
#print axioms NLA.Proofs.TR04.TensorFormat.Index
#assert_kind NLA.Proofs.TR04.TensorFormat.indexFintype "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.indexFintype
#print axioms NLA.Proofs.TR04.TensorFormat.indexFintype
#assert_kind NLA.Proofs.TR04.TensorFormat.Tensor "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Tensor
#print axioms NLA.Proofs.TR04.TensorFormat.Tensor
#assert_kind NLA.Proofs.TR04.TensorFormat.splitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.splitIndex
#print axioms NLA.Proofs.TR04.TensorFormat.splitIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.joinIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.joinIndex
#print axioms NLA.Proofs.TR04.TensorFormat.joinIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.joinIndex_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.joinIndex_zero
#print axioms NLA.Proofs.TR04.TensorFormat.joinIndex_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.join_splitIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.join_splitIndex
#print axioms NLA.Proofs.TR04.TensorFormat.join_splitIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.split_joinIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.split_joinIndex
#print axioms NLA.Proofs.TR04.TensorFormat.split_joinIndex
#assert_kind NLA.Proofs.TR04.TensorFormat.splitEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.splitEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.splitEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold
#print axioms NLA.Proofs.TR04.TensorFormat.unfold
#assert_kind NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.unfoldLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.energy "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy
#print axioms NLA.Proofs.TR04.TensorFormat.energy
#assert_kind NLA.Proofs.TR04.TensorFormat.error "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error
#print axioms NLA.Proofs.TR04.TensorFormat.error
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_nonneg
#print axioms NLA.Proofs.TR04.TensorFormat.energy_nonneg
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_unfold
#print axioms NLA.Proofs.TR04.TensorFormat.energy_unfold
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_zero
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_sub
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_sub
#assert_kind NLA.Proofs.TR04.TensorFormat.error_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_unfold
#print axioms NLA.Proofs.TR04.TensorFormat.error_unfold
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_zero
#print axioms NLA.Proofs.TR04.TensorFormat.energy_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.error_zero_right "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_zero_right
#print axioms NLA.Proofs.TR04.TensorFormat.error_zero_right
#assert_kind NLA.Proofs.TR04.TensorFormat.error_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_nonneg
#print axioms NLA.Proofs.TR04.TensorFormat.error_nonneg
#assert_kind NLA.Proofs.TR04.TensorFormat.card_index "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.card_index
#print axioms NLA.Proofs.TR04.TensorFormat.card_index
#assert_kind NLA.Proofs.TR04.TensorFormat.modeList "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.modeList
#print axioms NLA.Proofs.TR04.TensorFormat.modeList
#assert_kind NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn
#print axioms NLA.Proofs.TR04.TensorFormat.modeList_eq_ofFn
#assert_kind NLA.Proofs.TR04.TensorFormat.length_modeList "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.length_modeList
#print axioms NLA.Proofs.TR04.TensorFormat.length_modeList
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.vectorIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.ofFnIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalTensorLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.original_error_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_error_eq
#print axioms NLA.Proofs.TR04.TensorFormat.original_error_eq
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
#assert_kind NLA.Proofs.TR04.TensorFormat.firstMatrix "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.firstMatrix
#print axioms NLA.Proofs.TR04.TensorFormat.firstMatrix
#assert_kind NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.firstMatrixLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.contract "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contract
#print axioms NLA.Proofs.TR04.TensorFormat.contract
#assert_kind NLA.Proofs.TR04.TensorFormat.lift "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.lift
#print axioms NLA.Proofs.TR04.TensorFormat.lift
#assert_kind NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.firstMatrix_actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_zero
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_sub
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_sub
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_comp "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_comp
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_comp
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirst_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirst_one
#print axioms NLA.Proofs.TR04.TensorFormat.actFirst_one
#assert_kind NLA.Proofs.TR04.TensorFormat.contract_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contract_lift
#print axioms NLA.Proofs.TR04.TensorFormat.contract_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_firstMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_firstMatrix
#print axioms NLA.Proofs.TR04.TensorFormat.energy_firstMatrix
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_lift
#print axioms NLA.Proofs.TR04.TensorFormat.energy_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.error_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_lift
#print axioms NLA.Proofs.TR04.TensorFormat.error_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.inner "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.inner
#print axioms NLA.Proofs.TR04.TensorFormat.inner
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_add
#print axioms NLA.Proofs.TR04.TensorFormat.energy_add
#assert_kind NLA.Proofs.TR04.TensorFormat.inner_contract_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.inner_contract_lift
#print axioms NLA.Proofs.TR04.TensorFormat.inner_contract_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.residual_inner_lift "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.residual_inner_lift
#print axioms NLA.Proofs.TR04.TensorFormat.residual_inner_lift
#assert_kind NLA.Proofs.TR04.TensorFormat.error_lift_decomposition "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_lift_decomposition
#print axioms NLA.Proofs.TR04.TensorFormat.error_lift_decomposition
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_contract_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_contract_le
#print axioms NLA.Proofs.TR04.TensorFormat.energy_contract_le
#assert_kind NLA.Proofs.TR04.TensorFormat.error_contract_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_contract_le
#print axioms NLA.Proofs.TR04.TensorFormat.error_contract_le
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixAction "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixAction
#print axioms NLA.Proofs.TR04.TensorFormat.prefixAction
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_actFirst_succ
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_actFirst_le
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_contract_le
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_le
#assert_kind NLA.Proofs.TR04.TensorFormat.headIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.headIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.headIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_one_eq_submatrix
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_one
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_one
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_lift_one_le
#assert_kind NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.reindexLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_reindex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_reindex
#print axioms NLA.Proofs.TR04.TensorFormat.energy_reindex
#assert_kind NLA.Proofs.TR04.TensorFormat.error_reindex "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_reindex
#print axioms NLA.Proofs.TR04.TensorFormat.error_reindex
#assert_kind NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.mergeIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.merge "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.merge
#print axioms NLA.Proofs.TR04.TensorFormat.merge
#assert_kind NLA.Proofs.TR04.TensorFormat.merge_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.merge_apply
#print axioms NLA.Proofs.TR04.TensorFormat.merge_apply
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_merge
#print axioms NLA.Proofs.TR04.TensorFormat.energy_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.error_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_merge
#print axioms NLA.Proofs.TR04.TensorFormat.error_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_merge
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_merge "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_merge
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_merge
#assert_kind NLA.Proofs.TR04.TensorFormat.projected_error_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.projected_error_eq
#print axioms NLA.Proofs.TR04.TensorFormat.projected_error_eq
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
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixSize "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixSize
#print axioms NLA.Proofs.TR04.TensorFormat.suffixSize
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_denseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.rank_denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.energy_denseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.energy_denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_sub "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_sub
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_sub
#assert_kind NLA.Proofs.TR04.TensorFormat.cappedRank "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.cappedRank
#print axioms NLA.Proofs.TR04.TensorFormat.cappedRank
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixFrame
#print axioms NLA.Proofs.TR04.TensorFormat.prefixFrame
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal
#print axioms NLA.Proofs.TR04.TensorFormat.prefixFrame_orthonormal
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_prefix_projection
#assert_kind NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le
#print axioms NLA.Proofs.TR04.TensorFormat.error_prefix_projection_le
#assert_kind NLA.Proofs.TR04.TensorFormat.RankFeasible "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.RankFeasible
#print axioms NLA.Proofs.TR04.TensorFormat.RankFeasible
#assert_kind NLA.Proofs.TR04.TensorFormat.stepRank "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepRank
#print axioms NLA.Proofs.TR04.TensorFormat.stepRank
#assert_kind NLA.Proofs.TR04.TensorFormat.stepFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepFrame
#print axioms NLA.Proofs.TR04.TensorFormat.stepFrame
#assert_kind NLA.Proofs.TR04.TensorFormat.stepInput "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepInput
#print axioms NLA.Proofs.TR04.TensorFormat.stepInput
#assert_kind NLA.Proofs.TR04.TensorFormat.stepOutput "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.stepOutput
#print axioms NLA.Proofs.TR04.TensorFormat.stepOutput
#assert_kind NLA.Proofs.TR04.TensorFormat.Completion "inductive"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Completion
#print axioms NLA.Proofs.TR04.TensorFormat.Completion
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_exists "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_exists
#print axioms NLA.Proofs.TR04.TensorFormat.completion_exists
#assert_kind NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract
#print axioms NLA.Proofs.TR04.TensorFormat.rankFeasible_merge_contract
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_feasible
#print axioms NLA.Proofs.TR04.TensorFormat.completion_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveModes "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveModes
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveModes
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveRanks "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveRanks
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveRanks
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.step_length "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_length
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_length
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.StepBounds "inductive"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.StepBounds
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.StepBounds
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product
#assert_kind NLA.Proofs.TR04.TensorFormat.take_ofFn_modes "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.take_ofFn_modes
#print axioms NLA.Proofs.TR04.TensorFormat.take_ofFn_modes
#assert_kind NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes
#print axioms NLA.Proofs.TR04.TensorFormat.drop_ofFn_modes
#assert_kind NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.prefixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixPositionZeroEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixPositionSuccEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.suffixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate
#print axioms NLA.Proofs.TR04.TensorFormat.prefix_join_coordinate
#assert_kind NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate
#print axioms NLA.Proofs.TR04.TensorFormat.suffix_join_coordinate
#assert_kind NLA.Proofs.TR04.TensorFormat.originalCut_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalCut_le
#print axioms NLA.Proofs.TR04.TensorFormat.originalCut_le
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalRowPositionEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalColPositionEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRowEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRowEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalRowEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalColEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalColEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalColEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.original_join "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_join
#print axioms NLA.Proofs.TR04.TensorFormat.original_join
#assert_kind NLA.Proofs.TR04.TensorFormat.unfold_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfold_original
#print axioms NLA.Proofs.TR04.TensorFormat.unfold_original
#assert_kind NLA.Proofs.TR04.TensorFormat.rank_unfold_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_unfold_original
#print axioms NLA.Proofs.TR04.TensorFormat.rank_unfold_original
#assert_kind NLA.Proofs.TR04.TensorFormat.originalRanks "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRanks
#print axioms NLA.Proofs.TR04.TensorFormat.originalRanks
#assert_kind NLA.Proofs.TR04.TensorFormat.original_feasible_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_feasible_iff
#print axioms NLA.Proofs.TR04.TensorFormat.original_feasible_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.radixIndexEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset
#assert_kind NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_lt
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_lt
#assert_kind NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode
#assert_kind NLA.Proofs.TR04.TensorFormat.cardToProdEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.cardToProdEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.cardToProdEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val
#print axioms NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val
#assert_kind NLA.Proofs.TR04.TensorFormat.prod_modeList "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prod_modeList
#print axioms NLA.Proofs.TR04.TensorFormat.prod_modeList
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ
#assert_kind NLA.Proofs.TR04.TensorFormat.vectorOffset "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset
#assert_kind NLA.Proofs.TR04.TensorFormat.radixOffset_vector "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_vector
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_vector
#assert_kind NLA.Proofs.TR04.TensorFormat.original_radixOffset "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_radixOffset
#print axioms NLA.Proofs.TR04.TensorFormat.original_radixOffset
#assert_kind NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize
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
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable "inductive"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt
#assert_kind NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix

noncomputable section
open scoped BigOperators Matrix
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example {m : ℕ} {ns : List ℕ} :
    PositiveModes (m :: ns) ↔ 0 < m ∧ PositiveModes ns := @NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons m ns
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example {ns : List ℕ} (h : PositiveModes ns) : 0 < ns.prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (ns : List ℕ) : suffixSize ns = ns.prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod ns
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example {ns : List ℕ} (h : PositiveModes ns) : 0 < suffixSize ns := @NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example {ns : List ℕ} (h : PositiveModes ns) (m : ℕ) (hm : m ∈ ns) :
    m ≤ ns.prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod ns h m hm
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) : stepRank m ns r ≤ m := @NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows m ns r
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    stepRank m ns r ≤ suffixSize ns := @NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols m ns r
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) : stepRank m ns r ≤ r 0 := @NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request m ns r
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (hm : 0 < m) (hns : PositiveModes ns) (hr : 0 < r 0) : 0 < stepRank m ns r := @NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos m ns r hm hns hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    ((stepRank m (n :: ns) r * n) :: ns).prod ≤ (m :: n :: ns).prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le m n ns r
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    stepRank m ns r * suffixSize ns ≤ (m :: ns).prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le m ns r
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    ((stepRank m (n :: ns) r * n) :: ns).length + 1 = (m :: n :: ns).length := @NLA.Proofs.TR04.TensorFormat.Dimensions.step_length m n ns r
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (h : PositiveModes (m :: n :: ns)) (hr : PositiveRanks (m :: n :: ns) r) :
    PositiveModes ((stepRank m (n :: ns) r * n) :: ns) := @NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes m n ns r h hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (hr : PositiveRanks (m :: n :: ns) r) :
    PositiveRanks ((stepRank m (n :: ns) r * n) :: ns) (fun j => r (j + 1)) := @NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks m n ns r hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

example (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) (bound : ℕ)
    (hpos : PositiveModes (m :: n :: ns)) (hr : PositiveRanks (m :: n :: ns) r)
    (hprod : (m :: n :: ns).prod ≤ bound) : StepBounds m n ns r bound := @NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product m n ns r bound hpos hr hprod
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) (hpos : PositiveModes initial)
    (hr : PositiveRanks initial r) :
    PositiveModes ns ∧ PositiveRanks ns (fun j => r (level + j)) ∧
      ns.prod ≤ initial.prod ∧ ns.length + level = initial.length := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants initial ns r level h hpos hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example {initial ns : List ℕ} {r : ℕ → ℕ} {level m n : ℕ}
    (h : Reachable initial r level (m :: n :: ns))
    (hpos : PositiveModes initial) (hr : PositiveRanks initial r) :
    StepBounds m n ns (fun j => r (level + j)) initial.prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds initial ns r level m n h hpos hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) (hi : initial ≠ []) : ns ≠ [] := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty initial ns r level h hi
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (ns : List ℕ) (k : ℕ) : (ns.drop k).tail = ns.drop (k + 1) := @NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop ns k
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) : ns.tail = initial.drop (level + 1) := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop initial ns r level h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) (hi : initial ≠ [])
    (hpos : PositiveModes initial) (hr : PositiveRanks initial r) : level < initial.length := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt initial ns r level h hi hpos hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) : PositiveModes (modeList S.mode) := @NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original S
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j) :
    PositiveRanks (modeList S.mode) (originalRanks S r) := @NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original S r hr
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level ns) :
    PositiveModes ns ∧ PositiveRanks ns (fun j => originalRanks S r (level + j)) ∧
      ns.prod ≤ DenseSize S ∧ ns.length + level = S.order := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants S r hr level ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m :: n :: ns)) :
    StepBounds m n ns (fun j => originalRanks S r (level + j)) (DenseSize S) := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds S r hr level m n ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level ns) : level < S.order := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt S r hr level ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation
example (S : Shape) (r : Ranks S)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m :: n :: ns)) :
    suffixSize (n :: ns) = ((modeList S.mode).drop (level + 1)).prod := @NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix S r level m n ns h
end NLA.Proofs.TR04.TensorFormat.Dimensions

namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation

-- Derive the actual N-cell dense buffers and N^2 squares together, using only
-- original cut-rank positivity and literal recursive reachability.
example (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m :: n :: ns)) :
    0 < stepRank m (n :: ns) (fun j => originalRanks S r (level + j)) ∧
    m * suffixSize (n :: ns) ≤ DenseSize S ∧
    stepRank m (n :: ns) (fun j => originalRanks S r (level + j)) *
      suffixSize (n :: ns) ≤ DenseSize S ∧
    m * m ≤ DenseSize S ^ 2 ∧
    m * stepRank m (n :: ns) (fun j => originalRanks S r (level + j)) ≤ DenseSize S ^ 2 ∧
    suffixSize (n :: ns) * suffixSize (n :: ns) ≤ DenseSize S ^ 2 := by
  have b := h.original_step_bounds S r hr
  exact ⟨b.rank_pos, b.input_dense_le, b.contracted_dense_le,
    b.frame_square_le, b.frame_rectangle_le, b.right_square_le⟩

-- Even with zero modes or zero requested ranks, the actual child tensor's
-- index cardinality cannot exceed that of the parent input tensor.
example (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    Fintype.card (Index ((stepRank m (n :: ns) r * n) :: ns)) ≤
      Fintype.card (Index (m :: n :: ns)) := by
  calc
    Fintype.card (Index ((stepRank m (n :: ns) r * n) :: ns)) =
        ((stepRank m (n :: ns) r * n) :: ns).prod :=
      NLA.Proofs.TR04.TensorFormat.card_index _
    _ ≤ (m :: n :: ns).prod := step_prod_le m n ns r
    _ = Fintype.card (Index (m :: n :: ns)) :=
      (NLA.Proofs.TR04.TensorFormat.card_index _).symm

example (m n : ℕ) (ns : List ℕ) :
    stepRank m (n :: ns) (fun _ => 0) = 0 ∧
      ((stepRank m (n :: ns) (fun _ => 0) * n) :: ns).prod = 0 := by
  simp [stepRank, cappedRank]

end NLA.Proofs.TR04.TensorFormat.Dimensions

end
