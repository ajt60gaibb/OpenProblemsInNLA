import NLA.Proofs.TR04.TTCompletionOriginal
import NLA.Proofs.TR04.TTCompletionProjected
import NLA.Proofs.TR04.TensorCompressionLinear

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
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_comparator_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_comparator_bound
#print axioms NLA.Proofs.TR04.TensorFormat.completion_comparator_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.projected_completion_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.projected_completion_bound
#print axioms NLA.Proofs.TR04.TensorFormat.projected_completion_bound
#assert_kind NLA.Proofs.TR04.feasible_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.feasible_zero
#print axioms NLA.Proofs.TR04.feasible_zero
#assert_kind NLA.Proofs.TR04.feasible_nonempty "theorem"
#assert_trust kernel NLA.Proofs.TR04.feasible_nonempty
#print axioms NLA.Proofs.TR04.feasible_nonempty
#assert_kind NLA.Proofs.TR04.isClosed_matrix_rank_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.isClosed_matrix_rank_le
#print axioms NLA.Proofs.TR04.isClosed_matrix_rank_le
#assert_kind NLA.Proofs.TR04.isClosed_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.isClosed_feasible
#print axioms NLA.Proofs.TR04.isClosed_feasible
#assert_kind NLA.Proofs.TR04.continuous_frobeniusSq "theorem"
#assert_trust kernel NLA.Proofs.TR04.continuous_frobeniusSq
#print axioms NLA.Proofs.TR04.continuous_frobeniusSq
#assert_kind NLA.Proofs.TR04.frobeniusSq_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_nonneg
#print axioms NLA.Proofs.TR04.frobeniusSq_nonneg
#assert_kind NLA.Proofs.TR04.frobeniusSq_coordinate_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_coordinate_le
#print axioms NLA.Proofs.TR04.frobeniusSq_coordinate_le
#assert_kind NLA.Proofs.TR04.frobeniusSq_self "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_self
#print axioms NLA.Proofs.TR04.frobeniusSq_self
#assert_kind NLA.Proofs.TR04.frobeniusSq_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_eq_zero_iff
#print axioms NLA.Proofs.TR04.frobeniusSq_eq_zero_iff
#assert_kind NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box
#print axioms NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box
#assert_kind NLA.Proofs.TR04.exists_feasible_minimizer "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_feasible_minimizer
#print axioms NLA.Proofs.TR04.exists_feasible_minimizer
#assert_kind NLA.Proofs.TR04.exists_optimum "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_optimum
#print axioms NLA.Proofs.TR04.exists_optimum
#assert_kind NLA.Proofs.TR04.optimum_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.optimum_nonneg
#print axioms NLA.Proofs.TR04.optimum_nonneg
#assert_kind NLA.Proofs.TR04.optimum_le_of_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.optimum_le_of_feasible
#print axioms NLA.Proofs.TR04.optimum_le_of_feasible
#assert_kind NLA.Proofs.TR04.optimum_eq_zero_iff_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.optimum_eq_zero_iff_feasible
#print axioms NLA.Proofs.TR04.optimum_eq_zero_iff_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.OriginalCompletion "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.OriginalCompletion
#print axioms NLA.Proofs.TR04.TensorFormat.OriginalCompletion
#assert_kind NLA.Proofs.TR04.TensorFormat.original_completion_exists "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_completion_exists
#print axioms NLA.Proofs.TR04.TensorFormat.original_completion_exists
#assert_kind NLA.Proofs.TR04.TensorFormat.original_completion_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_completion_feasible
#print axioms NLA.Proofs.TR04.TensorFormat.original_completion_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.original_completion_comparator_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_completion_comparator_bound
#print axioms NLA.Proofs.TR04.TensorFormat.original_completion_comparator_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.original_completion_optimum_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_completion_optimum_bound
#print axioms NLA.Proofs.TR04.TensorFormat.original_completion_optimum_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.original_completion_exact_of_optimum_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_completion_exact_of_optimum_zero
#print axioms NLA.Proofs.TR04.TensorFormat.original_completion_exact_of_optimum_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.projected_completion_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.projected_completion_feasible
#print axioms NLA.Proofs.TR04.TensorFormat.projected_completion_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.exists_projected_completion "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.exists_projected_completion
#print axioms NLA.Proofs.TR04.TensorFormat.exists_projected_completion
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirstLinearMap "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirstLinearMap
#print axioms NLA.Proofs.TR04.TensorFormat.actFirstLinearMap
#assert_kind NLA.Proofs.TR04.TensorFormat.actFirstContinuousLinearMap "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actFirstContinuousLinearMap
#print axioms NLA.Proofs.TR04.TensorFormat.actFirstContinuousLinearMap
#assert_kind NLA.Proofs.TR04.TensorFormat.continuous_actFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.continuous_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.continuous_actFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.unfoldContinuousLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.unfoldContinuousLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.unfoldContinuousLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.mergeContinuousLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.mergeContinuousLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.mergeContinuousLinearEquiv
#assert_kind NLA.Proofs.TR04.TensorFormat.originalTensorContinuousLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalTensorContinuousLinearEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalTensorContinuousLinearEquiv

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04.TensorFormat
example (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    ∃ X, OriginalCompletion S r A X := @NLA.Proofs.TR04.TensorFormat.original_completion_exists S r A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X) : NLA.Computation.TensorTrainApproximation.Feasible S r X := @NLA.Proofs.TR04.TensorFormat.original_completion_feasible S r A X h
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X) :
    NLA.Computation.TensorTrainApproximation.FrobeniusSq S A X ≤
      ((S.order - 1 : ℕ) : ℝ) * NLA.Computation.TensorTrainApproximation.Optimum S r A := @NLA.Proofs.TR04.TensorFormat.original_completion_optimum_bound S r A X h
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example
    {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X)
    (hzero : NLA.Computation.TensorTrainApproximation.Optimum S r A = 0) : X = A := @NLA.Proofs.TR04.TensorFormat.original_completion_exact_of_optimum_zero S r A X h hzero
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example {m k n : ℕ} (ns : List ℕ) (r : ℕ → ℕ)
    (U : Matrix (Fin m) (Fin k) ℝ) (hU : SVD.OrthonormalColumns U) (hk : k ≤ r 0)
    (A : Tensor (m :: n :: ns)) :
    ∃ Z : Tensor ((k * n) :: ns),
      Completion ((k * n) :: ns) (fun j => r (j + 1))
        (merge k n ns (contract U A)) Z ∧
      RankFeasible (m :: n :: ns) r (lift U ((merge k n ns).symm Z)) ∧
      ∀ Y : Tensor (m :: n :: ns), RankFeasible (m :: n :: ns) r Y →
        error (m :: n :: ns) A (lift U ((merge k n ns).symm Z)) ≤
          error (m :: n :: ns) A (lift U (contract U A)) +
            (ns.length : ℝ) * energy (m :: n :: ns) (lift U (contract U (A - Y))) := @NLA.Proofs.TR04.TensorFormat.exists_projected_completion m k n ns r U hU hk A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example {m k n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y)
    {Z : Tensor ((k * n) :: ns)}
    (hZ : Completion ((k * n) :: ns) (fun j => r (j + 1))
      (merge k n ns (contract U A)) Z) :
    error (m :: n :: ns) A (lift U ((merge k n ns).symm Z)) ≤
      error (m :: n :: ns) A (lift U (contract U A)) +
        (ns.length : ℝ) * energy (m :: n :: ns) (lift U (contract U (A - Y))) := @NLA.Proofs.TR04.TensorFormat.projected_completion_bound m k n ns r U hU A Y hY Z hZ
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    Matrix.rank (unfold (modeList S.mode) (originalTensorLinearEquiv S A) (j.val + 1)) =
      Matrix.rank (NLA.Computation.TensorTrainApproximation.Unfold S A j) := @NLA.Proofs.TR04.TensorFormat.rank_unfold_original S j A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    NLA.Computation.TensorTrainApproximation.Feasible S r A ↔
      RankFeasible (modeList S.mode) (originalRanks S r) (originalTensorLinearEquiv S A) := @NLA.Proofs.TR04.TensorFormat.original_feasible_iff S r A
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A : Tensor (m :: ns)) (B : Tensor (k :: ns)) :
    error (m :: ns) A (lift U B) =
      error (m :: ns) A (lift U (contract U A)) + error (k :: ns) (contract U A) B := @NLA.Proofs.TR04.TensorFormat.error_lift_decomposition m k ns U hU A B
end NLA.Proofs.TR04.TensorFormat
namespace NLA.Proofs.TR04.TensorFormat
example {ns : List ℕ} {r : ℕ → ℕ} {A X : Tensor ns}
    (h : Completion ns r A X) (Y : Tensor ns) (hY : RankFeasible ns r Y) :
    error ns A X ≤ ((ns.length - 1 : ℕ) : ℝ) * error ns A Y := @NLA.Proofs.TR04.TensorFormat.completion_comparator_bound ns r A X h Y hY
end NLA.Proofs.TR04.TensorFormat
end
