import NLA.Proofs.TR04.TTStrictExplicitFamily

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
#assert_kind NLA.Proofs.TR04.TensorFormat.completion_comparator_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_comparator_bound
#print axioms NLA.Proofs.TR04.TensorFormat.completion_comparator_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.projected_completion_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.projected_completion_bound
#print axioms NLA.Proofs.TR04.TensorFormat.projected_completion_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.projected_completion_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.projected_completion_feasible
#print axioms NLA.Proofs.TR04.TensorFormat.projected_completion_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.exists_projected_completion "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.exists_projected_completion
#print axioms NLA.Proofs.TR04.TensorFormat.exists_projected_completion
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
#assert_kind NLA.Proofs.TR04.SVD.singularSubspace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace
#print axioms NLA.Proofs.TR04.SVD.singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.singularSubspace_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_le
#print axioms NLA.Proofs.TR04.SVD.singularSubspace_le
#assert_kind NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le
#print axioms NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le
#assert_kind NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual
#print axioms NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_matrixColumns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_matrixColumns
#print axioms NLA.Proofs.TR04.SVD.orthonormal_matrixColumns
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections
#print axioms NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections
#assert_kind NLA.Proofs.TR04.SVD.finrank_singularSubspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.finrank_singularSubspace
#print axioms NLA.Proofs.TR04.SVD.finrank_singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.starProjection_singularSubspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.starProjection_singularSubspace
#print axioms NLA.Proofs.TR04.SVD.starProjection_singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace
#print axioms NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace
#assert_kind NLA.Proofs.TR04.SVD.validSVD_selected_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_selected_energy
#print axioms NLA.Proofs.TR04.SVD.validSVD_selected_energy
#assert_kind NLA.Proofs.TR04.SVD.validSVD_selected_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_selected_error
#print axioms NLA.Proofs.TR04.SVD.validSVD_selected_error
#assert_kind NLA.Proofs.TR04.SVD.cyclicWindow "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicWindow
#print axioms NLA.Proofs.TR04.SVD.cyclicWindow
#assert_kind NLA.Proofs.TR04.SVD.cyclicTranslate "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicTranslate
#print axioms NLA.Proofs.TR04.SVD.cyclicTranslate
#assert_kind NLA.Proofs.TR04.SVD.cyclicDifference "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicDifference
#print axioms NLA.Proofs.TR04.SVD.cyclicDifference
#assert_kind NLA.Proofs.TR04.SVD.prefixSubtypeEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixSubtypeEquiv
#print axioms NLA.Proofs.TR04.SVD.prefixSubtypeEquiv
#assert_kind NLA.Proofs.TR04.SVD.card_cyclicWindow "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.card_cyclicWindow
#print axioms NLA.Proofs.TR04.SVD.card_cyclicWindow
#assert_kind NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator
#print axioms NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator
#assert_kind NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy
#print axioms NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy
#assert_kind NLA.Proofs.TR04.SVD.average_cyclicWindow_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.average_cyclicWindow_energy
#print axioms NLA.Proofs.TR04.SVD.average_cyclicWindow_energy
#assert_kind NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average
#print axioms NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average
#assert_kind NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal
#print axioms NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.norm_singularSubspace_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_singularSubspace_projection
#print axioms NLA.Proofs.TR04.SVD.norm_singularSubspace_projection
#assert_kind NLA.Proofs.TR04.SVD.singularCoordinateEnergy "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularCoordinateEnergy
#print axioms NLA.Proofs.TR04.SVD.singularCoordinateEnergy
#assert_kind NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg
#print axioms NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg
#assert_kind NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy
#print axioms NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy
#assert_kind NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le
#print axioms NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le
#assert_kind NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns
#print axioms NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns
#assert_kind NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le
#print axioms NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le
#assert_kind NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank
#print axioms NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank
#assert_kind NLA.Proofs.TR04.SVD.rank_selected_projection_le_card "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_selected_projection_le_card
#print axioms NLA.Proofs.TR04.SVD.rank_selected_projection_le_card
#assert_kind NLA.Proofs.TR04.SVD.selectedFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.selectedFrame
#print axioms NLA.Proofs.TR04.SVD.selectedFrame
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame
#assert_kind NLA.Proofs.TR04.SVD.orthonormalColumns_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_rank
#print axioms NLA.Proofs.TR04.SVD.orthonormalColumns_rank
#assert_kind NLA.Proofs.TR04.SVD.rank_selectedFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_selectedFrame
#print axioms NLA.Proofs.TR04.SVD.rank_selectedFrame
#assert_kind NLA.Proofs.TR04.SVD.tieEmbedding "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieEmbedding
#print axioms NLA.Proofs.TR04.SVD.tieEmbedding
#assert_kind NLA.Proofs.TR04.SVD.tieEmbedding_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieEmbedding_injective
#print axioms NLA.Proofs.TR04.SVD.tieEmbedding_injective
#assert_kind NLA.Proofs.TR04.SVD.prefixDirections "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixDirections
#print axioms NLA.Proofs.TR04.SVD.prefixDirections
#assert_kind NLA.Proofs.TR04.SVD.tieDirections "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieDirections
#print axioms NLA.Proofs.TR04.SVD.tieDirections
#assert_kind NLA.Proofs.TR04.SVD.windowDirections "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.windowDirections
#print axioms NLA.Proofs.TR04.SVD.windowDirections
#assert_kind NLA.Proofs.TR04.SVD.tieSelection "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieSelection
#print axioms NLA.Proofs.TR04.SVD.tieSelection
#assert_kind NLA.Proofs.TR04.SVD.prefix_window_disjoint "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_window_disjoint
#print axioms NLA.Proofs.TR04.SVD.prefix_window_disjoint
#assert_kind NLA.Proofs.TR04.SVD.card_tieSelection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.card_tieSelection
#print axioms NLA.Proofs.TR04.SVD.card_tieSelection
#assert_kind NLA.Proofs.TR04.SVD.sum_tieSelection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection
#print axioms NLA.Proofs.TR04.SVD.sum_tieSelection
#assert_kind NLA.Proofs.TR04.SVD.sum_all_tieSelections "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_all_tieSelections
#print axioms NLA.Proofs.TR04.SVD.sum_all_tieSelections
#assert_kind NLA.Proofs.TR04.SVD.sum_indicator_finset "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_indicator_finset
#print axioms NLA.Proofs.TR04.SVD.sum_indicator_finset
#assert_kind NLA.Proofs.TR04.SVD.directionSubspace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.directionSubspace
#print axioms NLA.Proofs.TR04.SVD.directionSubspace
#assert_kind NLA.Proofs.TR04.SVD.directionSubspace_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.directionSubspace_project_energy
#print axioms NLA.Proofs.TR04.SVD.directionSubspace_project_energy
#assert_kind NLA.Proofs.TR04.SVD.rank_directionFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_directionFrame
#print axioms NLA.Proofs.TR04.SVD.rank_directionFrame
#assert_kind NLA.Proofs.TR04.SVD.rank_directionProjection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_directionProjection_le
#print axioms NLA.Proofs.TR04.SVD.rank_directionProjection_le
#assert_kind NLA.Proofs.TR04.SVD.rank_tieSelectionFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_tieSelectionFrame
#print axioms NLA.Proofs.TR04.SVD.rank_tieSelectionFrame
#assert_kind NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le
#print axioms NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le
#assert_kind NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy
#print axioms NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy
#assert_kind NLA.Proofs.TR04.SVD.average_tieSelection_project_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.average_tieSelection_project_energy
#print axioms NLA.Proofs.TR04.SVD.average_tieSelection_project_energy
#assert_kind NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le
#print axioms NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le
#assert_kind NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le
#print axioms NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le
#assert_kind NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin
#print axioms NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin
#assert_kind NLA.Proofs.TR04.SVD.sum_prefixDirections "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_prefixDirections
#print axioms NLA.Proofs.TR04.SVD.sum_prefixDirections
#assert_kind NLA.Proofs.TR04.SVD.prefixEnergy_tie_split "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy_tie_split
#print axioms NLA.Proofs.TR04.SVD.prefixEnergy_tie_split
#assert_kind NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block
#print axioms NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block
#assert_kind NLA.Proofs.TR04.SVD.validSVD_tieSelection_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_tieSelection_error
#print axioms NLA.Proofs.TR04.SVD.validSVD_tieSelection_error
#assert_kind NLA.Proofs.TR04.SVD.card_filter_fin_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.card_filter_fin_lt
#print axioms NLA.Proofs.TR04.SVD.card_filter_fin_lt
#assert_kind NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card
#print axioms NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card
#assert_kind NLA.Proofs.TR04.SVD.TieStructure "inductive"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure
#print axioms NLA.Proofs.TR04.SVD.TieStructure
#assert_kind NLA.Proofs.TR04.SVD.exists_tieStructure "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_tieStructure
#print axioms NLA.Proofs.TR04.SVD.exists_tieStructure
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.tied_pos "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.tied_pos
#print axioms NLA.Proofs.TR04.SVD.TieStructure.tied_pos
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equal_embedding "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equal_embedding
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equal_embedding
#assert_kind NLA.Proofs.TR04.SVD.mem_prefixDirections_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.mem_prefixDirections_iff
#print axioms NLA.Proofs.TR04.SVD.mem_prefixDirections_iff
#assert_kind NLA.Proofs.TR04.SVD.tieSelection_val_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.tieSelection_val_lt
#print axioms NLA.Proofs.TR04.SVD.tieSelection_val_lt
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.above_subspace "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.above_subspace
#print axioms NLA.Proofs.TR04.SVD.TieStructure.above_subspace
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.first_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.first_error
#print axioms NLA.Proofs.TR04.SVD.TieStructure.first_error
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.frame_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.frame_rank
#print axioms NLA.Proofs.TR04.SVD.TieStructure.frame_rank
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual
#assert_kind NLA.Proofs.TR04.SVD.prefix_weights_eq_one "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_weights_eq_one
#print axioms NLA.Proofs.TR04.SVD.prefix_weights_eq_one
#assert_kind NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights
#print axioms NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero
#print axioms NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual
#print axioms NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual
#assert_kind NLA.Proofs.TR04.SVD.starProjection_span_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.starProjection_span_orthonormal
#print axioms NLA.Proofs.TR04.SVD.starProjection_span_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.frameSpace "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.frameSpace
#print axioms NLA.Proofs.TR04.SVD.frameSpace
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_frameColumns "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_frameColumns
#print axioms NLA.Proofs.TR04.SVD.orthonormal_frameColumns
#assert_kind NLA.Proofs.TR04.SVD.frame_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.frame_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.frame_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix
#print axioms NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix
#assert_kind NLA.Proofs.TR04.SVD.exists_directionFrame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_directionFrame
#print axioms NLA.Proofs.TR04.SVD.exists_directionFrame
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.exists_frame "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.exists_frame
#print axioms NLA.Proofs.TR04.SVD.TieStructure.exists_frame
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.error_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.error_eq_zero_iff
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.error_eq_zero_iff
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.error_denseFirst "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.error_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.error_denseFirst
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_le
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_le
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_eq
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_eq
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.error_projection_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.error_projection_eq
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.error_projection_eq
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.IsMinimum "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.IsMinimum
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.IsMinimum
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.exists_minimum "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.exists_minimum
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.exists_minimum
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_bound
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_strict_of_first_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_strict_of_first_lt
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_strict_of_first_lt
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.FirstFrames "inductive"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.FirstFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.FirstFrames
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames_first_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames_first_error
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames_first_error
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.exists_firstFrames "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.exists_firstFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.exists_firstFrames
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.rank_denseFirst_le_first "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.rank_denseFirst_le_first
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.rank_denseFirst_le_first
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.family_first_error "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_first_error
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.family_first_error
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.family_projected_energy "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_projected_energy
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.family_projected_energy
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_feasible
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_feasible
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_bound "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_bound
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_bound
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.family_min_strict "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_min_strict
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.family_min_strict
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_exact_of_error_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_exact_of_error_zero
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_exact_of_error_zero
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.exists_strict_family "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.exists_strict_family
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.exists_strict_family
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_val
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_val
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem
#assert_kind NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_space "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_space
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_space
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_rank
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_rank
#assert_kind NLA.Proofs.TR04.SVD.cyclicFrame_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_projection
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_projection
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure_above "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_above
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_above
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure_tied "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_tied
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_tied
#assert_kind NLA.Proofs.TR04.SVD.countedTieStructure_take "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_take
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_take
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection
#assert_kind NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames "definition"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_positive "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_positive
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_positive
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_large "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_large
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_large
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_nonpos "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_nonpos
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_nonpos
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_width "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_width
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_width
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec
#assert_kind NLA.Proofs.TR04.TensorFormat.TTStrict.explicit_strict_family "theorem"
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicit_strict_family
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicit_strict_family

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04.SVD

example {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (k : Fin (h + s)) :
    (cyclicColumnIndex h t ht s hst j k).val =
      if k.val < h then k.val else h + ((j.val + (k.val - h)) % t) := @NLA.Proofs.TR04.SVD.cyclicColumnIndex_val p h t (inferInstance) ht s hst j k
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    Function.Injective (cyclicColumnIndex h t ht s hst j) := @NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective p h t (inferInstance) ht s hst j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (x : Fin p)
    (hx : x ∈ tieSelection h t ht s j) :
    ∃ k : Fin (h + s), cyclicColumnIndex h t ht s hst j k = x := @NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective p h t (inferInstance) ht s hst j x hx
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    Matrix.rank (cyclicFrame U ht s hst j) = h + s := @NLA.Proofs.TR04.SVD.cyclicFrame_rank m l h t (inferInstance) U hU ht s hst j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t)
    (B : Matrix (Fin m) (Fin l) ℝ) :
    cyclicFrame U ht s hst j * ((cyclicFrame U ht s hst j).transpose * B) =
      projectMatrix (directionSubspace U (tieSelection h t ht s j)) B := @NLA.Proofs.TR04.SVD.cyclicFrame_projection m l h t (inferInstance) U hU ht s hst j B
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (a : Fin p) :
    (countedTieStructure sigma hord a).above =
      (Finset.univ.filter (fun k => sigma a < sigma k)).card := @NLA.Proofs.TR04.SVD.countedTieStructure_above p sigma hord a
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (a : Fin p) :
    (countedTieStructure sigma hord a).tied =
      (Finset.univ.filter (fun k => sigma a ≤ sigma k)).card -
        (Finset.univ.filter (fun k => sigma a < sigma k)).card := @NLA.Proofs.TR04.SVD.countedTieStructure_tied p sigma hord a
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (a : Fin p) :
    (countedTieStructure sigma hord a).take = a.val + 1 -
      (Finset.univ.filter (fun k => sigma a < sigma k)).card := @NLA.Proofs.TR04.SVD.countedTieStructure_take p sigma hord a
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (j : Fin T.tied) (k : Fin (a.val + 1)) :
    (T.explicitIndex j k).val = if k.val < T.above then k.val
      else T.above + ((j.val + (k.val - T.above)) % T.tied) := @NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val p sigma a T j k
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD

example {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) (B : Matrix (Fin m) (Fin l) ℝ) :
    T.explicitFrame U j * ((T.explicitFrame U j).transpose * B) =
      projectMatrix (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B := @NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection m l U hU sigma a T j B
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine
example {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l)
    (j : Fin (positiveFrames h r hr hrp).count) (i : Fin m)
    (k : Fin (positiveFrames h r hr hrp).width) :
    let a : Fin (min m l) := ⟨r - 1, by omega⟩
    let T := SVD.countedTieStructure sigma h.2.2.2.1 a
    (positiveFrames h r hr hrp).frame j i k =
      U i (Fin.castLE (Nat.min_le_left m l) (T.explicitIndex j k)) := @NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column m l B U sigma V h r hr hrp j i k
end NLA.Proofs.TR04.TensorFormat.TTStrict
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine
example {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l) :
    let a : Fin (min m l) := ⟨r - 1, by omega⟩
    (positiveFrames h r hr hrp).count =
      (Finset.univ.filter (fun k => sigma a ≤ sigma k)).card -
        (Finset.univ.filter (fun k => sigma a < sigma k)).card := @NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count m l B U sigma V h r hr hrp
end NLA.Proofs.TR04.TensorFormat.TTStrict
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine
example {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) (hr : 1 ≤ r) :
    let F := explicitFirstFrames h r
    F.count ≤ min m l + 1 ∧ F.width ≤ min m l ∧
      (∀ j, SVD.matrixEnergy (B - F.frame j * ((F.frame j).transpose * B)) =
        SVD.tailEnergy sigma r) ∧
      ∀ Y : Matrix (Fin m) (Fin l) ℝ, Matrix.rank Y ≤ r →
        SVD.matrixEnergy (B - Y) = SVD.tailEnergy sigma r →
        0 < SVD.matrixEnergy (B - Y) →
        ∃ j, SVD.matrixEnergy (F.frame j * ((F.frame j).transpose * (B - Y))) <
          SVD.matrixEnergy (B - Y) := @NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec m l B U sigma V h r hr
end NLA.Proofs.TR04.TensorFormat.TTStrict
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine
example {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (hlen : 1 ≤ ns.length) (hr : 1 ≤ r 0) {A : Tensor (m :: n :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) :
    let F := explicitFirstFrames h (r 0)
    F.count ≤ min m (suffixSize (n :: ns)) + 1 ∧
      F.width ≤ min m (suffixSize (n :: ns)) ∧
      (∃ Z : Fin F.count → Tensor ((F.width * n) :: ns),
        ∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
          (merge F.width n ns (contract (F.frame j) A)) (Z j)) ∧
      ∀ Z : Fin F.count → Tensor ((F.width * n) :: ns),
        (∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
          (merge F.width n ns (contract (F.frame j) A)) (Z j)) →
        (∃ imin, IsMinimum A (fun j => completionOutput (F.frame j) (Z j)) imin) ∧
        ∀ imin, IsMinimum A (fun j => completionOutput (F.frame j) (Z j)) imin →
          RankFeasible (m :: n :: ns) r (completionOutput (F.frame imin) (Z imin)) ∧
          ∀ Y : Tensor (m :: n :: ns), RankFeasible (m :: n :: ns) r Y →
            (0 < error (m :: n :: ns) A Y →
              error (m :: n :: ns) A (completionOutput (F.frame imin) (Z imin)) <
                ((ns.length : ℝ) + 1) * error (m :: n :: ns) A Y) ∧
            (error (m :: n :: ns) A Y = 0 → completionOutput (F.frame imin) (Z imin) = A) := @NLA.Proofs.TR04.TensorFormat.TTStrict.explicit_strict_family m n ns r hlen hr A U sigma V h
end NLA.Proofs.TR04.TensorFormat.TTStrict
end
