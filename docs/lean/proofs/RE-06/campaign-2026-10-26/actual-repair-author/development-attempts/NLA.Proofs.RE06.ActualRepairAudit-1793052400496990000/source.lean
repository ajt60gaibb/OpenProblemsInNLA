import NLA.Proofs.RE06.RepairMeasurable
import NLA.Proofs.RE06.RepairAudit

set_option autoImplicit false
set_option leancert.trust "kernel"

#repair_theorem NLA.Proofs.RE06.Repair.subspaceMatrix_gram
#assert_trust kernel NLA.Proofs.RE06.Repair.subspaceMatrix_gram
#print axioms NLA.Proofs.RE06.Repair.subspaceMatrix_gram

#repair_theorem NLA.Proofs.RE06.Repair.subspaceMatrix_map
#assert_trust kernel NLA.Proofs.RE06.Repair.subspaceMatrix_map
#print axioms NLA.Proofs.RE06.Repair.subspaceMatrix_map

#repair_theorem NLA.Proofs.RE06.Repair.subspaceMatrix_range
#assert_trust kernel NLA.Proofs.RE06.Repair.subspaceMatrix_range
#print axioms NLA.Proofs.RE06.Repair.subspaceMatrix_range

#repair_theorem NLA.Proofs.RE06.Repair.rangeDimension_le
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeDimension_le
#print axioms NLA.Proofs.RE06.Repair.rangeDimension_le

#repair_theorem NLA.Proofs.RE06.Repair.rangeBasisMatrix_gram
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeBasisMatrix_gram
#print axioms NLA.Proofs.RE06.Repair.rangeBasisMatrix_gram

#repair_theorem NLA.Proofs.RE06.Repair.rangeBasisMatrix_range
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeBasisMatrix_range
#print axioms NLA.Proofs.RE06.Repair.rangeBasisMatrix_range

#repair_theorem NLA.Proofs.RE06.Repair.actualProjector_transpose
#assert_trust kernel NLA.Proofs.RE06.Repair.actualProjector_transpose
#print axioms NLA.Proofs.RE06.Repair.actualProjector_transpose

#repair_theorem NLA.Proofs.RE06.Repair.actualProjector_mul
#assert_trust kernel NLA.Proofs.RE06.Repair.actualProjector_mul
#print axioms NLA.Proofs.RE06.Repair.actualProjector_mul

#repair_theorem NLA.Proofs.RE06.Repair.actualProjector_idempotent
#assert_trust kernel NLA.Proofs.RE06.Repair.actualProjector_idempotent
#print axioms NLA.Proofs.RE06.Repair.actualProjector_idempotent

#repair_theorem NLA.Proofs.RE06.Repair.actualProjector_basis
#assert_trust kernel NLA.Proofs.RE06.Repair.actualProjector_basis
#print axioms NLA.Proofs.RE06.Repair.actualProjector_basis

#repair_theorem NLA.Proofs.RE06.Repair.actualRangeResidual_basis
#assert_trust kernel NLA.Proofs.RE06.Repair.actualRangeResidual_basis
#print axioms NLA.Proofs.RE06.Repair.actualRangeResidual_basis

#repair_theorem NLA.Proofs.RE06.Repair.actualRangeResidual_orthogonal
#assert_trust kernel NLA.Proofs.RE06.Repair.actualRangeResidual_orthogonal
#print axioms NLA.Proofs.RE06.Repair.actualRangeResidual_orthogonal

#repair_theorem NLA.Proofs.RE06.Repair.actualRangeResidual_orthogonal_factor
#assert_trust kernel NLA.Proofs.RE06.Repair.actualRangeResidual_orthogonal_factor
#print axioms NLA.Proofs.RE06.Repair.actualRangeResidual_orthogonal_factor

#repair_theorem NLA.Proofs.RE06.Repair.actualRegressionEnergy_nonneg
#assert_trust kernel NLA.Proofs.RE06.Repair.actualRegressionEnergy_nonneg
#print axioms NLA.Proofs.RE06.Repair.actualRegressionEnergy_nonneg

#repair_theorem NLA.Proofs.RE06.Repair.actual_repair_pythagoras
#assert_trust kernel NLA.Proofs.RE06.Repair.actual_repair_pythagoras
#print axioms NLA.Proofs.RE06.Repair.actual_repair_pythagoras

#repair_theorem NLA.Proofs.RE06.Repair.actualRegressionEnergy_basis
#assert_trust kernel NLA.Proofs.RE06.Repair.actualRegressionEnergy_basis
#print axioms NLA.Proofs.RE06.Repair.actualRegressionEnergy_basis

#repair_theorem NLA.Proofs.RE06.Repair.weighted_rangefinder_error
#assert_trust kernel NLA.Proofs.RE06.Repair.weighted_rangefinder_error
#print axioms NLA.Proofs.RE06.Repair.weighted_rangefinder_error

#repair_theorem NLA.Proofs.RE06.Repair.weighted_rangefinder_majorant
#assert_trust kernel NLA.Proofs.RE06.Repair.weighted_rangefinder_majorant
#print axioms NLA.Proofs.RE06.Repair.weighted_rangefinder_majorant

#repair_theorem NLA.Proofs.RE06.Repair.headEmbedding_gram
#assert_trust kernel NLA.Proofs.RE06.Repair.headEmbedding_gram
#print axioms NLA.Proofs.RE06.Repair.headEmbedding_gram

#repair_theorem NLA.Proofs.RE06.Repair.tailDiagonal_head
#assert_trust kernel NLA.Proofs.RE06.Repair.tailDiagonal_head
#print axioms NLA.Proofs.RE06.Repair.tailDiagonal_head

#repair_theorem NLA.Proofs.RE06.Repair.headEmbedding_projector
#assert_trust kernel NLA.Proofs.RE06.Repair.headEmbedding_projector
#print axioms NLA.Proofs.RE06.Repair.headEmbedding_projector

#repair_theorem NLA.Proofs.RE06.Repair.headEmbedding_diagonal
#assert_trust kernel NLA.Proofs.RE06.Repair.headEmbedding_diagonal
#print axioms NLA.Proofs.RE06.Repair.headEmbedding_diagonal

#repair_theorem NLA.Proofs.RE06.Repair.diagonal_head_tail
#assert_trust kernel NLA.Proofs.RE06.Repair.diagonal_head_tail
#print axioms NLA.Proofs.RE06.Repair.diagonal_head_tail

#repair_theorem NLA.Proofs.RE06.Repair.headEmbedding_isometry
#assert_trust kernel NLA.Proofs.RE06.Repair.headEmbedding_isometry
#print axioms NLA.Proofs.RE06.Repair.headEmbedding_isometry

#repair_theorem NLA.Proofs.RE06.Repair.residual_svd_partition
#assert_trust kernel NLA.Proofs.RE06.Repair.residual_svd_partition
#print axioms NLA.Proofs.RE06.Repair.residual_svd_partition

#repair_theorem NLA.Proofs.RE06.Repair.residual_tail_energy
#assert_trust kernel NLA.Proofs.RE06.Repair.residual_tail_energy
#print axioms NLA.Proofs.RE06.Repair.residual_tail_energy

#repair_theorem NLA.Proofs.RE06.Repair.residual_tail_weighted_orthogonal
#assert_trust kernel NLA.Proofs.RE06.Repair.residual_tail_weighted_orthogonal
#print axioms NLA.Proofs.RE06.Repair.residual_tail_weighted_orthogonal

#repair_theorem NLA.Proofs.RE06.Repair.tailRandomEnergy_nonneg
#assert_trust kernel NLA.Proofs.RE06.Repair.tailRandomEnergy_nonneg
#print axioms NLA.Proofs.RE06.Repair.tailRandomEnergy_nonneg

#repair_theorem NLA.Proofs.RE06.Repair.actual_rangefinder_majorant
#assert_trust kernel NLA.Proofs.RE06.Repair.actual_rangefinder_majorant
#print axioms NLA.Proofs.RE06.Repair.actual_rangefinder_majorant

#repair_theorem NLA.Proofs.RE06.Repair.actualExcessMajorant_nonneg
#assert_trust kernel NLA.Proofs.RE06.Repair.actualExcessMajorant_nonneg
#print axioms NLA.Proofs.RE06.Repair.actualExcessMajorant_nonneg

#repair_theorem NLA.Proofs.RE06.Repair.actual_svd_repair_majorant
#assert_trust kernel NLA.Proofs.RE06.Repair.actual_svd_repair_majorant
#print axioms NLA.Proofs.RE06.Repair.actual_svd_repair_majorant

#repair_theorem NLA.Proofs.RE06.Repair.measurable_matrix_sub
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_matrix_sub
#print axioms NLA.Proofs.RE06.Repair.measurable_matrix_sub

#repair_theorem NLA.Proofs.RE06.Repair.measurable_squaredFrobenius_zero
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_squaredFrobenius_zero
#print axioms NLA.Proofs.RE06.Repair.measurable_squaredFrobenius_zero

#repair_theorem NLA.Proofs.RE06.Repair.measurable_actualProjector
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_actualProjector
#print axioms NLA.Proofs.RE06.Repair.measurable_actualProjector

#repair_theorem NLA.Proofs.RE06.Repair.measurable_actualRangeResidual
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_actualRangeResidual
#print axioms NLA.Proofs.RE06.Repair.measurable_actualRangeResidual

#repair_theorem NLA.Proofs.RE06.Repair.measurable_actualRegressionEnergy
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_actualRegressionEnergy
#print axioms NLA.Proofs.RE06.Repair.measurable_actualRegressionEnergy

#repair_theorem NLA.Proofs.RE06.Repair.measurable_tailRandomEnergy
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_tailRandomEnergy
#print axioms NLA.Proofs.RE06.Repair.measurable_tailRandomEnergy

#repair_theorem NLA.Proofs.RE06.Repair.measurable_actualExcessMajorant
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_actualExcessMajorant
#print axioms NLA.Proofs.RE06.Repair.measurable_actualExcessMajorant

#repair_theorem NLA.Proofs.RE06.Repair.measurable_repairErrorFromEntries
#assert_trust kernel NLA.Proofs.RE06.Repair.measurable_repairErrorFromEntries
#print axioms NLA.Proofs.RE06.Repair.measurable_repairErrorFromEntries

#repair_theorem NLA.Proofs.RE06.Repair.measurableSet_repairFailureSet
#assert_trust kernel NLA.Proofs.RE06.Repair.measurableSet_repairFailureSet
#print axioms NLA.Proofs.RE06.Repair.measurableSet_repairFailureSet

#repair_theorem NLA.Proofs.RE06.Repair.nullMeasurableSet_repairFailureSet
#assert_trust kernel NLA.Proofs.RE06.Repair.nullMeasurableSet_repairFailureSet
#print axioms NLA.Proofs.RE06.Repair.nullMeasurableSet_repairFailureSet

#assert_trust kernel NLA.Proofs.RE06.Repair.RealSpace
#print axioms NLA.Proofs.RE06.Repair.RealSpace

#assert_trust kernel NLA.Proofs.RE06.Repair.subspaceBasis
#print axioms NLA.Proofs.RE06.Repair.subspaceBasis

#assert_trust kernel NLA.Proofs.RE06.Repair.subspaceMatrix
#print axioms NLA.Proofs.RE06.Repair.subspaceMatrix

#assert_trust kernel NLA.Proofs.RE06.Repair.rangeDimension
#print axioms NLA.Proofs.RE06.Repair.rangeDimension

#assert_trust kernel NLA.Proofs.RE06.Repair.rangeBasisMatrix
#print axioms NLA.Proofs.RE06.Repair.rangeBasisMatrix

#assert_trust kernel NLA.Proofs.RE06.Repair.actualProjector
#print axioms NLA.Proofs.RE06.Repair.actualProjector

#assert_trust kernel NLA.Proofs.RE06.Repair.actualRangeResidual
#print axioms NLA.Proofs.RE06.Repair.actualRangeResidual

#assert_trust kernel NLA.Proofs.RE06.Repair.actualRegressionEnergy
#print axioms NLA.Proofs.RE06.Repair.actualRegressionEnergy

#assert_trust kernel NLA.Proofs.RE06.Repair.headEmbedding
#print axioms NLA.Proofs.RE06.Repair.headEmbedding

#assert_trust kernel NLA.Proofs.RE06.Repair.tailDiagonal
#print axioms NLA.Proofs.RE06.Repair.tailDiagonal

#assert_trust kernel NLA.Proofs.RE06.Repair.headDiagonal
#print axioms NLA.Proofs.RE06.Repair.headDiagonal

#assert_trust kernel NLA.Proofs.RE06.Repair.headCoordinates
#print axioms NLA.Proofs.RE06.Repair.headCoordinates

#assert_trust kernel NLA.Proofs.RE06.Repair.tailRandomEnergy
#print axioms NLA.Proofs.RE06.Repair.tailRandomEnergy

#assert_trust kernel NLA.Proofs.RE06.Repair.actualExcessMajorant
#print axioms NLA.Proofs.RE06.Repair.actualExcessMajorant
