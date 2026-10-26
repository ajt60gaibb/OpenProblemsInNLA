import NLA.Proofs.TR04.SVDCore
import NLA.Proofs.TR04.SVDTotal
import NLA.Proofs.TR04.SVDEnergy
import NLA.Proofs.TR04.SVDRank
import NLA.Proofs.TR04.SVDWeights
import NLA.Proofs.TR04.SVDProjection
import NLA.Proofs.TR04.SVDEckartYoung
import NLA.Proofs.TR04.SVDEckartEquality
import NLA.Proofs.TR04.SVDThresholdWeights
import NLA.Proofs.TR04.SVDEckartThreshold
import NLA.Proofs.TR04.SVDConsequences
import NLA.Proofs.TR04.SVDResidual
import NLA.Proofs.TR04.SVDFrameProjection
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

noncomputable section
open NLA.Computation.SVDMachine NLA.Proofs.TR04.SVD
example (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ) :
    ∃ U sigma V, ValidSVD B U sigma V := exists_validSVD B
example (l : ℕ) (B : Matrix (Fin 0) (Fin l) ℝ) :
    ∃ U sigma V, ValidSVD B U sigma V := exists_validSVD B
example (m : ℕ) (B : Matrix (Fin m) (Fin 0) ℝ) :
    ∃ U sigma V, ValidSVD B U sigma V := exists_validSVD B
section
variable {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
example (r : ℕ) (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r) :
    tailEnergy sigma r ≤ matrixEnergy (B - Y) := validSVD_eckartYoung h r Y hY
example (r : ℕ) : matrixEnergy (B - truncate U sigma V r) = tailEnergy sigma r :=
  validSVD_truncate_error h r
example (r : ℕ) : Matrix.rank (truncate U sigma V r) ≤ r ∧
    ∀ Y, Matrix.rank Y ≤ r → matrixEnergy (B - truncate U sigma V r) ≤ matrixEnergy (B - Y) :=
  validSVD_truncate_best h r
example (r : ℕ) : Matrix.rank B ≤ r ↔ tailEnergy sigma r = 0 :=
  validSVD_rank_le_iff_tail_zero h r
example (a : Fin (min m l)) (ha : 0 < sigma a)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = a.val + 1 ∧
      (∀ k, sigma a < sigma k → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =
          matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧
      (∀ k, sigma k < sigma a → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) :=
  validSVD_eckartYoung_eq_last_retained h a ha Y hY heq
example (r : ℕ) (hr : r ≤ min m l) (tau : ℝ) (htau : 0 < tau)
    (habove : ∀ k, k.val < r → tau ≤ sigma k)
    (hbelow : ∀ k, r ≤ k.val → sigma k ≤ tau)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma r) :
    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = r ∧
      (∀ k, tau < sigma k → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =
          matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧
      (∀ k, sigma k < tau → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) :=
  validSVD_eckartYoung_eq_threshold h r hr tau htau habove hbelow Y hY heq
example (q : ℕ) (hq : q ≤ min m l) :
    (U.submatrix id (Fin.castLE (hq.trans (Nat.min_le_left m l)))).transpose * B =
      fun a j => sigma (Fin.castLE hq a) *
        V j (Fin.castLE (Nat.min_le_right m l) (Fin.castLE hq a)) :=
  validSVD_prefix_coefficients h q hq
example (r : ℕ) :
    let q := min r (min m l)
    let Q := U.submatrix id (Fin.castLE
      ((Nat.min_le_right r (min m l)).trans (Nat.min_le_left m l)))
    Q * (Q.transpose * B) = truncate U sigma V r := validSVD_prefix_projection h r
example (a : Fin (min m l)) (ha : 0 < sigma a)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    singularSubspace U (fun k => sigma a < sigma k) ≤ columnSpace Y ∧
      projectMatrix (singularSubspace U (fun k => sigma a < sigma k)) (B - Y) = 0 :=
  validSVD_equality_above_span_residual h a ha Y hY heq
end
end
