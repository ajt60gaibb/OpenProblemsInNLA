import NLA.Proofs.TR04.SVDConsequences
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace TR04SVDAuthorConsumer
open NLA.Proofs.TR04.SVD NLA.Computation.SVDMachine
 theorem literal_total {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ) :
 ∃ U sigma V, NLA.Computation.SVDMachine.ValidSVD B U sigma V := exists_validSVD B
 theorem literal_best {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ)
 (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
 (V : Matrix (Fin l) (Fin l) ℝ) (h : ValidSVD B U sigma V) (r : ℕ)
 (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r) :
 (∑ k, if r ≤ k.val then (sigma k)^2 else 0) ≤
 ∑ i, ∑ j, (B i j - Y i j)^2 := validSVD_eckartYoung h r Y hY
 theorem literal_tail {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ)
 (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
 (V : Matrix (Fin l) (Fin l) ℝ) (h : ValidSVD B U sigma V) (r : ℕ) :
 Matrix.rank (truncate U sigma V r) ≤ r ∧
 matrixEnergy (B - truncate U sigma V r) = ∑ k, if r ≤ k.val then (sigma k)^2 else 0 :=
 ⟨truncate_rank_le U sigma V r, validSVD_truncate_error h r⟩
#assert_trust kernel literal_total
#assert_trust kernel literal_best
#assert_trust kernel literal_tail
#print axioms literal_total
#print axioms literal_best
#print axioms literal_tail
end TR04SVDAuthorConsumer
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
