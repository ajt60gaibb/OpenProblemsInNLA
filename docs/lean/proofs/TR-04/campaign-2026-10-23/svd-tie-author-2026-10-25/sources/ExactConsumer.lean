import NLA.Proofs.TR04.SVDFrameSpace
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace TR04TieAuthorConsumer
open NLA.Proofs.TR04.SVD NLA.Computation.SVDMachine
 theorem literal_complete_block {p : ℕ} (sigma : Fin p → ℝ) (h : Antitone sigma) (a : Fin p) :
 Nonempty (TieStructure sigma a) := exists_tieStructure sigma h a
 theorem literal_first_error {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
 {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
 {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
 {a : Fin (min m l)} (T : TieStructure sigma a) (j : Fin T.tied) :
 matrixEnergy (B - projectMatrix
 (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B) =
 tailEnergy sigma (a.val + 1) := T.first_error h j
 theorem literal_strict_residual {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
 {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
 {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
 {a : Fin (min m l)} (T : TieStructure sigma a) (ha : 0 < sigma a)
 (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
 (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1))
 (hpos : 0 < matrixEnergy (B - Y)) :
 ∃ j : Fin T.tied, matrixEnergy (projectMatrix
 (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) (B - Y)) <
 matrixEnergy (B - Y) := T.equality_exists_strict_residual h ha Y hY heq hpos
 theorem literal_frame {m l : ℕ} {U : Matrix (Fin m) (Fin m) ℝ}
 (hU : OrthonormalColumns U) {sigma : Fin (min m l) → ℝ}
 {a : Fin (min m l)} (T : TieStructure sigma a) (j : Fin T.tied) :
 ∃ Q : Matrix (Fin m) (Fin (a.val + 1)) ℝ, OrthonormalColumns Q ∧
 ∀ B : Matrix (Fin m) (Fin l) ℝ, Q * (Q.transpose * B) = projectMatrix (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B := T.exists_frame hU j
#assert_trust kernel literal_complete_block
#assert_trust kernel literal_first_error
#assert_trust kernel literal_strict_residual
#assert_trust kernel literal_frame
#print axioms literal_complete_block
#print axioms literal_first_error
#print axioms literal_strict_residual
#print axioms literal_frame
end TR04TieAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.SVD.Space
#assert_trust kernel NLA.Proofs.TR04.SVD.rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_image_rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.inner_image_rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_domain
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#assert_trust kernel NLA.Proofs.TR04.SVD.leftVector
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_leftBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_truncate
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_validSVD
#assert_trust kernel NLA.Proofs.TR04.SVD.OrthonormalColumns
#assert_trust kernel NLA.Proofs.TR04.SVD.transpose_mul_eq_one
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_submatrix
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_inner
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_sum_sq
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy
#assert_trust kernel NLA.Proofs.TR04.SVD.synthesis
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eq_synthesis
#assert_trust kernel NLA.Proofs.TR04.SVD.synthesis_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.synthesis_sub
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_error_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.truncate
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_truncate_error
#assert_trust kernel NLA.Proofs.TR04.SVD.truncate_rank_le
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_nonneg
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_entry_sq_le
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_eq_zero_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixError_eq_zero_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_zero_tail_iff_truncate
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy_nonneg
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy
#assert_trust kernel NLA.Proofs.TR04.SVD.weightDefect
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_count
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_prefix_defect
#assert_trust kernel NLA.Proofs.TR04.SVD.weightDefect_nonneg
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_prefix_le
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_prefix_eq_support
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_projectMatrix
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_sub
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixEnergy_eq_sum_column_norm
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_energy_decomposition
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_error_decomposition
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_error_le
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_error_eq_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_basis_of_orthonormalColumns
#assert_trust kernel NLA.Proofs.TR04.SVD.projection_norm_sq_basis_sum
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_nonneg
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_le_one
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_projectionWeight
#assert_trust kernel NLA.Proofs.TR04.SVD.right_synthesis_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_synthesis
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_project_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_prefix_le
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_svd_projectionWeight_le
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSquares_antitone
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_add_tail
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_of_length_le
#assert_trust kernel NLA.Proofs.TR04.SVD.columnSpace
#assert_trust kernel NLA.Proofs.TR04.SVD.matrixColumn_mem_columnSpace
#assert_trust kernel NLA.Proofs.TR04.SVD.finrank_columnSpace
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_eq_one_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_eq_zero_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq
#assert_trust kernel NLA.Proofs.TR04.SVD.thresholdDefect
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_count_of_le
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_threshold_defect
#assert_trust kernel NLA.Proofs.TR04.SVD.thresholdDefect_nonneg
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_threshold_le
#assert_trust kernel NLA.Proofs.TR04.SVD.weighted_threshold_eq_support
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_threshold
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_eckartYoung_eq_last_retained
#assert_trust kernel NLA.Proofs.TR04.SVD.tailEnergy_eq_zero_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_rank_le_iff_tail_zero
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_truncate_best
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_positive_tail
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_le
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_projection
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_matrixColumns
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_selected_singularDirections
#assert_trust kernel NLA.Proofs.TR04.SVD.finrank_singularSubspace
#assert_trust kernel NLA.Proofs.TR04.SVD.starProjection_singularSubspace
#assert_trust kernel NLA.Proofs.TR04.SVD.projectionWeight_singularSubspace
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_selected_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_selected_error
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicWindow
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicTranslate
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicDifference
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixSubtypeEquiv
#assert_trust kernel NLA.Proofs.TR04.SVD.card_cyclicWindow
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_cyclicWindow_indicator
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_cyclicWindow_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.average_cyclicWindow_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_cyclicWindow_energy_le_average
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_starProjection_span_orthonormal
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_singularSubspace_projection
#assert_trust kernel NLA.Proofs.TR04.SVD.singularCoordinateEnergy
#assert_trust kernel NLA.Proofs.TR04.SVD.singularCoordinateEnergy_nonneg
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_projectMatrix_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_singularCoordinateEnergy_le
#assert_trust kernel NLA.Proofs.TR04.SVD.toEuclideanLin_eq_sum_columns
#assert_trust kernel NLA.Proofs.TR04.SVD.toEuclideanLin_projectMatrix
#assert_trust kernel NLA.Proofs.TR04.SVD.columnSpace_projectMatrix_le
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_projectMatrix_le_finrank
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_selected_projection_le_card
#assert_trust kernel NLA.Proofs.TR04.SVD.selectedFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_selectedFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormalColumns_rank
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_selectedFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.tieEmbedding
#assert_trust kernel NLA.Proofs.TR04.SVD.tieEmbedding_injective
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixDirections
#assert_trust kernel NLA.Proofs.TR04.SVD.tieDirections
#assert_trust kernel NLA.Proofs.TR04.SVD.windowDirections
#assert_trust kernel NLA.Proofs.TR04.SVD.tieSelection
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_window_disjoint
#assert_trust kernel NLA.Proofs.TR04.SVD.card_tieSelection
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_all_tieSelections
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_indicator_finset
#assert_trust kernel NLA.Proofs.TR04.SVD.directionSubspace
#assert_trust kernel NLA.Proofs.TR04.SVD.directionSubspace_project_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_directionFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_directionProjection_le
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_tieSelectionFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.rank_tieSelectionProjection_le
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection_project_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.average_tieSelection_project_energy
#assert_trust kernel NLA.Proofs.TR04.SVD.average_tieSelection_project_energy_le
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_tieSelection_project_energy_le
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy_eq_sum_fin
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_prefixDirections
#assert_trust kernel NLA.Proofs.TR04.SVD.prefixEnergy_tie_split
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_tieSelection_constant_block
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_tieSelection_error
#assert_trust kernel NLA.Proofs.TR04.SVD.card_filter_fin_lt
#assert_trust kernel NLA.Proofs.TR04.SVD.lower_predicate_iff_lt_card
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_tieStructure
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.tied_pos
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equal_embedding
#assert_trust kernel NLA.Proofs.TR04.SVD.mem_prefixDirections_iff
#assert_trust kernel NLA.Proofs.TR04.SVD.tieSelection_val_lt
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.above_subspace
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.first_error
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.frame_rank
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_above_residual_zero
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_average_residual
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_exists_small_residual
#assert_trust kernel NLA.Proofs.TR04.SVD.prefix_weights_eq_one
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_sum_projectionWeights
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.full_equality_residual_zero
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.equality_exists_strict_residual
#assert_trust kernel NLA.Proofs.TR04.SVD.starProjection_span_orthonormal
#assert_trust kernel NLA.Proofs.TR04.SVD.frameSpace
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_frameColumns
#assert_trust kernel NLA.Proofs.TR04.SVD.frame_projectMatrix
#assert_trust kernel NLA.Proofs.TR04.SVD.selectedFrame_projectMatrix
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_directionFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.exists_frame
