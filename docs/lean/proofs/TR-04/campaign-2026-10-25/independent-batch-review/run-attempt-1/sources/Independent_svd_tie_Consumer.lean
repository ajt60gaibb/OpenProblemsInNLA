import NLA.Proofs.TR04.SVDFrameSpace

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
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#assert_kind NLA.Proofs.TR04.SVD.validSVD_prefix_projection "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#print axioms NLA.Proofs.TR04.SVD.validSVD_prefix_projection
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

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04.SVD
example {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (a : Fin p) : Nonempty (TieStructure sigma a) := @NLA.Proofs.TR04.SVD.exists_tieStructure p sigma hord a
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) : (tieSelection h t ht s j).card = h + s := @NLA.Proofs.TR04.SVD.card_tieSelection p h t (inferInstance) ht s hst j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) :
    matrixEnergy (B - projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B) =
        tailEnergy sigma (a.val + 1) := @NLA.Proofs.TR04.SVD.TieStructure.first_error m l B U sigma V h a T j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) :
    Matrix.rank (selectedFrame U (fun k =>
      k ∈ tieSelection T.above T.tied T.fits T.take j)) = a.val + 1 := @NLA.Proofs.TR04.SVD.TieStructure.frame_rank m l U hU sigma a T j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    (∑ j : Fin T.tied, matrixEnergy (projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) (B - Y))) / T.tied =
        ((T.take : ℝ) / T.tied) * matrixEnergy
          (projectMatrix (directionSubspace U (tieDirections T.above T.tied T.fits)) (B - Y)) := @NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual m l B U sigma V h a T ha Y hY heq
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (hfull : T.take = T.tied)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) (j : Fin T.tied) :
    projectMatrix (directionSubspace U (tieSelection T.above T.tied T.fits T.take j))
      (B - Y) = 0 := @NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero m l B U sigma V h a T ha hfull Y hY heq j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1))
    (hpos : 0 < matrixEnergy (B - Y)) :
    ∃ j : Fin T.tied, matrixEnergy (projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) (B - Y)) <
        matrixEnergy (B - Y) := @NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual m l B U sigma V h a T ha Y hY heq hpos
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) :
    ∃ Q : Matrix (Fin m) (Fin (a.val + 1)) ℝ, OrthonormalColumns Q ∧
      ∀ B : Matrix (Fin m) (Fin l) ℝ,
        Q * (Q.transpose * B) = projectMatrix
          (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B := @NLA.Proofs.TR04.SVD.TieStructure.exists_frame m l U hU sigma a T j
end NLA.Proofs.TR04.SVD
namespace NLA.Proofs.TR04.SVD
example {m l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix (Fin m) ι ℝ} (hQ : OrthonormalColumns Q)
    (B : Matrix (Fin m) (Fin l) ℝ) :
    projectMatrix (frameSpace Q) B = Q * (Q.transpose * B) := @NLA.Proofs.TR04.SVD.frame_projectMatrix m l ι (inferInstance) (inferInstance) Q hQ B
end NLA.Proofs.TR04.SVD
end
