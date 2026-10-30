import NLA.Proofs.RE06.GaussianMomentProjection
import NLA.Proofs.RE06.GaussianMomentAlgebra
import NLA.Proofs.RE06.PseudoInverseRankEvents
import NLA.Statements.RE06
import Reviewed.RE06

set_option autoImplicit false
set_option leancert.trust "kernel"

open Lean Elab Command in
elab "#actual_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected actual theorem declaration"

#actual_theorem NLA.Proofs.RE06.Pseudo.svd_U_gram
#assert_trust kernel NLA.Proofs.RE06.Pseudo.svd_U_gram
#print axioms NLA.Proofs.RE06.Pseudo.svd_U_gram
#actual_theorem NLA.Proofs.RE06.Pseudo.svd_V_gram
#assert_trust kernel NLA.Proofs.RE06.Pseudo.svd_V_gram
#print axioms NLA.Proofs.RE06.Pseudo.svd_V_gram
#actual_theorem NLA.Proofs.RE06.Pseudo.svd_U_cogram
#assert_trust kernel NLA.Proofs.RE06.Pseudo.svd_U_cogram
#print axioms NLA.Proofs.RE06.Pseudo.svd_U_cogram
#actual_theorem NLA.Proofs.RE06.Pseudo.svd_V_cogram
#assert_trust kernel NLA.Proofs.RE06.Pseudo.svd_V_cogram
#print axioms NLA.Proofs.RE06.Pseudo.svd_V_cogram
#actual_theorem NLA.Proofs.RE06.Pseudo.thinU_orthogonal
#assert_trust kernel NLA.Proofs.RE06.Pseudo.thinU_orthogonal
#print axioms NLA.Proofs.RE06.Pseudo.thinU_orthogonal
#actual_theorem NLA.Proofs.RE06.Pseudo.thinV_orthogonal
#assert_trust kernel NLA.Proofs.RE06.Pseudo.thinV_orthogonal
#print axioms NLA.Proofs.RE06.Pseudo.thinV_orthogonal
#actual_theorem NLA.Proofs.RE06.Pseudo.reconstruction
#assert_trust kernel NLA.Proofs.RE06.Pseudo.reconstruction
#print axioms NLA.Proofs.RE06.Pseudo.reconstruction
#actual_theorem NLA.Proofs.RE06.Pseudo.pseudoinverse_decomposition
#assert_trust kernel NLA.Proofs.RE06.Pseudo.pseudoinverse_decomposition
#print axioms NLA.Proofs.RE06.Pseudo.pseudoinverse_decomposition
#actual_theorem NLA.Proofs.RE06.Pseudo.diagonal_sigma_inv_sigma
#assert_trust kernel NLA.Proofs.RE06.Pseudo.diagonal_sigma_inv_sigma
#print axioms NLA.Proofs.RE06.Pseudo.diagonal_sigma_inv_sigma
#actual_theorem NLA.Proofs.RE06.Pseudo.diagonal_inv_sigma_inv
#assert_trust kernel NLA.Proofs.RE06.Pseudo.diagonal_inv_sigma_inv
#print axioms NLA.Proofs.RE06.Pseudo.diagonal_inv_sigma_inv
#actual_theorem NLA.Proofs.RE06.Pseudo.diagonal_sigma_inv_commute
#assert_trust kernel NLA.Proofs.RE06.Pseudo.diagonal_sigma_inv_commute
#print axioms NLA.Proofs.RE06.Pseudo.diagonal_sigma_inv_commute
#actual_theorem NLA.Proofs.RE06.Pseudo.mul_pseudoinverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.mul_pseudoinverse
#print axioms NLA.Proofs.RE06.Pseudo.mul_pseudoinverse
#actual_theorem NLA.Proofs.RE06.Pseudo.pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE06.Pseudo.pseudoinverse_mul
#print axioms NLA.Proofs.RE06.Pseudo.pseudoinverse_mul
#actual_theorem NLA.Proofs.RE06.Pseudo.sandwich_contract
#assert_trust kernel NLA.Proofs.RE06.Pseudo.sandwich_contract
#print axioms NLA.Proofs.RE06.Pseudo.sandwich_contract
#actual_theorem NLA.Proofs.RE06.Pseudo.sandwich_diagonal_transpose
#assert_trust kernel NLA.Proofs.RE06.Pseudo.sandwich_diagonal_transpose
#print axioms NLA.Proofs.RE06.Pseudo.sandwich_diagonal_transpose
#actual_theorem NLA.Proofs.RE06.Pseudo.mul_pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE06.Pseudo.mul_pseudoinverse_mul
#print axioms NLA.Proofs.RE06.Pseudo.mul_pseudoinverse_mul
#actual_theorem NLA.Proofs.RE06.Pseudo.pseudoinverse_mul_pseudoinverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.pseudoinverse_mul_pseudoinverse
#print axioms NLA.Proofs.RE06.Pseudo.pseudoinverse_mul_pseudoinverse
#actual_theorem NLA.Proofs.RE06.Pseudo.mul_pseudoinverse_transpose
#assert_trust kernel NLA.Proofs.RE06.Pseudo.mul_pseudoinverse_transpose
#print axioms NLA.Proofs.RE06.Pseudo.mul_pseudoinverse_transpose
#actual_theorem NLA.Proofs.RE06.Pseudo.pseudoinverse_mul_transpose
#assert_trust kernel NLA.Proofs.RE06.Pseudo.pseudoinverse_mul_transpose
#print axioms NLA.Proofs.RE06.Pseudo.pseudoinverse_mul_transpose
#actual_theorem NLA.Proofs.RE06.Pseudo.actual_isMP
#assert_trust kernel NLA.Proofs.RE06.Pseudo.actual_isMP
#print axioms NLA.Proofs.RE06.Pseudo.actual_isMP
#actual_theorem NLA.Proofs.RE06.Pseudo.symmetric_absorption_unique
#assert_trust kernel NLA.Proofs.RE06.Pseudo.symmetric_absorption_unique
#print axioms NLA.Proofs.RE06.Pseudo.symmetric_absorption_unique
#actual_theorem NLA.Proofs.RE06.Pseudo.isMP_unique
#assert_trust kernel NLA.Proofs.RE06.Pseudo.isMP_unique
#print axioms NLA.Proofs.RE06.Pseudo.isMP_unique
#actual_theorem NLA.Proofs.RE06.Pseudo.actual_eq_of_isMP
#assert_trust kernel NLA.Proofs.RE06.Pseudo.actual_eq_of_isMP
#print axioms NLA.Proofs.RE06.Pseudo.actual_eq_of_isMP
#actual_theorem NLA.Proofs.RE06.Pseudo.zero
#assert_trust kernel NLA.Proofs.RE06.Pseudo.zero
#print axioms NLA.Proofs.RE06.Pseudo.zero
#actual_theorem NLA.Proofs.RE06.Pseudo.transpose
#assert_trust kernel NLA.Proofs.RE06.Pseudo.transpose
#print axioms NLA.Proofs.RE06.Pseudo.transpose
#actual_theorem NLA.Proofs.RE06.Pseudo.mul_actual_eq_one_of_right_inverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.mul_actual_eq_one_of_right_inverse
#print axioms NLA.Proofs.RE06.Pseudo.mul_actual_eq_one_of_right_inverse
#actual_theorem NLA.Proofs.RE06.Pseudo.actual_mul_eq_one_of_left_inverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.actual_mul_eq_one_of_left_inverse
#print axioms NLA.Proofs.RE06.Pseudo.actual_mul_eq_one_of_left_inverse
#actual_theorem NLA.Proofs.RE06.Pseudo.full_row_formula
#assert_trust kernel NLA.Proofs.RE06.Pseudo.full_row_formula
#print axioms NLA.Proofs.RE06.Pseudo.full_row_formula
#actual_theorem NLA.Proofs.RE06.Pseudo.full_column_formula
#assert_trust kernel NLA.Proofs.RE06.Pseudo.full_column_formula
#print axioms NLA.Proofs.RE06.Pseudo.full_column_formula
#actual_theorem NLA.Proofs.RE06.Pseudo.orthonormal_columns
#assert_trust kernel NLA.Proofs.RE06.Pseudo.orthonormal_columns
#print axioms NLA.Proofs.RE06.Pseudo.orthonormal_columns
#actual_theorem NLA.Proofs.RE06.Pseudo.reverse_order
#assert_trust kernel NLA.Proofs.RE06.Pseudo.reverse_order
#print axioms NLA.Proofs.RE06.Pseudo.reverse_order
#actual_theorem NLA.Proofs.RE06.Pseudo.reverse_order_of_gram_det
#assert_trust kernel NLA.Proofs.RE06.Pseudo.reverse_order_of_gram_det
#print axioms NLA.Proofs.RE06.Pseudo.reverse_order_of_gram_det
#actual_theorem NLA.Proofs.RE06.Pseudo.repair_range_factorization
#assert_trust kernel NLA.Proofs.RE06.Pseudo.repair_range_factorization
#print axioms NLA.Proofs.RE06.Pseudo.repair_range_factorization
#actual_theorem NLA.Proofs.RE06.Pseudo.repair_range_factorization_of_gram_det
#assert_trust kernel NLA.Proofs.RE06.Pseudo.repair_range_factorization_of_gram_det
#print axioms NLA.Proofs.RE06.Pseudo.repair_range_factorization_of_gram_det
#actual_theorem NLA.Proofs.RE06.Pseudo.range_subset_iff_matrix_factor
#assert_trust kernel NLA.Proofs.RE06.Pseudo.range_subset_iff_matrix_factor
#print axioms NLA.Proofs.RE06.Pseudo.range_subset_iff_matrix_factor
#actual_theorem NLA.Proofs.RE06.Pseudo.repair_orthonormal_range
#assert_trust kernel NLA.Proofs.RE06.Pseudo.repair_orthonormal_range
#print axioms NLA.Proofs.RE06.Pseudo.repair_orthonormal_range
#actual_theorem NLA.Proofs.RE06.Pseudo.measurable_nonsing_inverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.measurable_nonsing_inverse
#print axioms NLA.Proofs.RE06.Pseudo.measurable_nonsing_inverse
#actual_theorem NLA.Proofs.RE06.Pseudo.measurable_matrix_mul
#assert_trust kernel NLA.Proofs.RE06.Pseudo.measurable_matrix_mul
#print axioms NLA.Proofs.RE06.Pseudo.measurable_matrix_mul
#actual_theorem NLA.Proofs.RE06.Pseudo.measurable_matrix_transpose
#assert_trust kernel NLA.Proofs.RE06.Pseudo.measurable_matrix_transpose
#print axioms NLA.Proofs.RE06.Pseudo.measurable_matrix_transpose
#actual_theorem NLA.Proofs.RE06.Pseudo.measurable_full_row_representative
#assert_trust kernel NLA.Proofs.RE06.Pseudo.measurable_full_row_representative
#print axioms NLA.Proofs.RE06.Pseudo.measurable_full_row_representative
#actual_theorem NLA.Proofs.RE06.Pseudo.aemeasurable_actual_of_full_row
#assert_trust kernel NLA.Proofs.RE06.Pseudo.aemeasurable_actual_of_full_row
#print axioms NLA.Proofs.RE06.Pseudo.aemeasurable_actual_of_full_row
#actual_theorem NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_of_right_inverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_of_right_inverse
#print axioms NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_of_right_inverse
#actual_theorem NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_iff_right_inverse
#assert_trust kernel NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_iff_right_inverse
#print axioms NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_iff_right_inverse
#actual_theorem NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_iff_surjective
#assert_trust kernel NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_iff_surjective
#print axioms NLA.Proofs.RE06.Pseudo.gram_det_ne_zero_iff_surjective
#actual_theorem NLA.Proofs.RE06.Pseudo.measurableSet_full_row_rank
#assert_trust kernel NLA.Proofs.RE06.Pseudo.measurableSet_full_row_rank
#print axioms NLA.Proofs.RE06.Pseudo.measurableSet_full_row_rank
#actual_theorem NLA.Proofs.RE06.Pseudo.frobeniusSq_nonneg
#assert_trust kernel NLA.Proofs.RE06.Pseudo.frobeniusSq_nonneg
#print axioms NLA.Proofs.RE06.Pseudo.frobeniusSq_nonneg
#actual_theorem NLA.Proofs.RE06.Pseudo.frobeniusSq_trace
#assert_trust kernel NLA.Proofs.RE06.Pseudo.frobeniusSq_trace
#print axioms NLA.Proofs.RE06.Pseudo.frobeniusSq_trace
#actual_theorem NLA.Proofs.RE06.Pseudo.full_row_inverse_gram
#assert_trust kernel NLA.Proofs.RE06.Pseudo.full_row_inverse_gram
#print axioms NLA.Proofs.RE06.Pseudo.full_row_inverse_gram
#actual_theorem NLA.Proofs.RE06.Pseudo.full_row_frobeniusSq_trace_inverse_gram
#assert_trust kernel NLA.Proofs.RE06.Pseudo.full_row_frobeniusSq_trace_inverse_gram
#print axioms NLA.Proofs.RE06.Pseudo.full_row_frobeniusSq_trace_inverse_gram
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gammaPDFReal_inverse_weight
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gammaPDFReal_inverse_weight
#print axioms NLA.Proofs.RE06.GaussianMoment.gammaPDFReal_inverse_weight
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gamma_inverse_lintegral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gamma_inverse_lintegral
#print axioms NLA.Proofs.RE06.GaussianMoment.gamma_inverse_lintegral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gamma_ae_nonneg
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gamma_ae_nonneg
#print axioms NLA.Proofs.RE06.GaussianMoment.gamma_ae_nonneg
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gamma_inverse_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gamma_inverse_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.gamma_inverse_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gamma_inverse_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gamma_inverse_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.gamma_inverse_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.scalar_inverse_laplace
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.scalar_inverse_laplace
#print axioms NLA.Proofs.RE06.GaussianMoment.scalar_inverse_laplace
#actual_theorem NLA.Proofs.RE06.GaussianMoment.affine_power_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.affine_power_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.affine_power_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.affine_power_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.affine_power_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.affine_power_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_nonneg
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_nonneg
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_nonneg
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_pos_ae
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_pos_ae
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_pos_ae
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_laplace
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_laplace
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_laplace
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_laplace_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_laplace_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_laplace_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_laplace_lintegral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_laplace_lintegral
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_laplace_lintegral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_inverse_lintegral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_inverse_lintegral
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_inverse_lintegral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral_of_hasLaw
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral_of_hasLaw
#print axioms NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral_of_hasLaw
#actual_theorem NLA.Proofs.RE06.GaussianMoment.stream_normSq_inverse_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.stream_normSq_inverse_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.stream_normSq_inverse_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.coisometry_adjoint_norm_sq
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.coisometry_adjoint_norm_sq
#print axioms NLA.Proofs.RE06.GaussianMoment.coisometry_adjoint_norm_sq
#actual_theorem NLA.Proofs.RE06.GaussianMoment.stdGaussian_map_coisometry
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.stdGaussian_map_coisometry
#print axioms NLA.Proofs.RE06.GaussianMoment.stdGaussian_map_coisometry
#actual_theorem NLA.Proofs.RE06.GaussianMoment.coisometry_coordinates_hasLaw
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.coisometry_coordinates_hasLaw
#print axioms NLA.Proofs.RE06.GaussianMoment.coisometry_coordinates_hasLaw
#actual_theorem NLA.Proofs.RE06.GaussianMoment.projected_normSq_inverse_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.projected_normSq_inverse_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.projected_normSq_inverse_integral

namespace NLA.Proofs.RE06.PseudoAudit
theorem live_frozen_identity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl
#assert_trust kernel live_frozen_identity
end NLA.Proofs.RE06.PseudoAudit
