import NLA.Proofs.RE06.PseudoInverseGlobalAudit
import NLA.Proofs.RE06.GaussianMomentTransport

set_option autoImplicit false
set_option leancert.trust "kernel"

#actual_theorem NLA.Proofs.RE06.GaussianMoment.inverse_block_first_entry
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.inverse_block_first_entry
#print axioms NLA.Proofs.RE06.GaussianMoment.inverse_block_first_entry
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowStack_gram
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowStack_gram
#print axioms NLA.Proofs.RE06.GaussianMoment.rowStack_gram
#actual_theorem NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry
#print axioms NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowComplement_transpose
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowComplement_transpose
#print axioms NLA.Proofs.RE06.GaussianMoment.rowComplement_transpose
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowComplement_idempotent
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowComplement_idempotent
#print axioms NLA.Proofs.RE06.GaussianMoment.rowComplement_idempotent
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_complement
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_complement
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_complement
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_residual_normSq
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_residual_normSq
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_residual_normSq
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_nonneg
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_nonneg
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_nonneg
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowStack_gram_det
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowStack_gram_det
#print axioms NLA.Proofs.RE06.GaussianMoment.rowStack_gram_det
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_pos
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_pos
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_pos
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowComplement_mulVec
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowComplement_mulVec
#print axioms NLA.Proofs.RE06.GaussianMoment.rowComplement_mulVec
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowComplement_killed
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowComplement_killed
#print axioms NLA.Proofs.RE06.GaussianMoment.rowComplement_killed
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowComplement_fix_kernel
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowComplement_fix_kernel
#print axioms NLA.Proofs.RE06.GaussianMoment.rowComplement_fix_kernel
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowComplement_range
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowComplement_range
#print axioms NLA.Proofs.RE06.GaussianMoment.rowComplement_range
#actual_theorem NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_residual
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_residual
#print axioms NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_residual
#actual_theorem NLA.Proofs.RE06.GaussianMoment.kernelCoordinates_coisometry
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.kernelCoordinates_coisometry
#print axioms NLA.Proofs.RE06.GaussianMoment.kernelCoordinates_coisometry
#actual_theorem NLA.Proofs.RE06.GaussianMoment.kernelDimension_eq
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.kernelDimension_eq
#print axioms NLA.Proofs.RE06.GaussianMoment.kernelDimension_eq
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowKernel_projection
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowKernel_projection
#print axioms NLA.Proofs.RE06.GaussianMoment.rowKernel_projection
#actual_theorem NLA.Proofs.RE06.GaussianMoment.kernelCoordinates_normSq
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.kernelCoordinates_normSq
#print axioms NLA.Proofs.RE06.GaussianMoment.kernelCoordinates_normSq
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_kernel_normSq
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_kernel_normSq
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_kernel_normSq
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_inverse_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_inverse_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_inverse_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_inverse_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_inverse_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_inverse_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowSchur_pos_ae
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowSchur_pos_ae
#print axioms NLA.Proofs.RE06.GaussianMoment.rowSchur_pos_ae
#actual_theorem NLA.Proofs.RE06.GaussianMoment.rowStack_gram_det_ne_zero_ae
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.rowStack_gram_det_ne_zero_ae
#print axioms NLA.Proofs.RE06.GaussianMoment.rowStack_gram_det_ne_zero_ae
#actual_theorem NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_ae
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_ae
#print axioms NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_ae
#actual_theorem NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.inverse_gram_first_entry_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.finRowStack_submatrix
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.finRowStack_submatrix
#print axioms NLA.Proofs.RE06.GaussianMoment.finRowStack_submatrix
#actual_theorem NLA.Proofs.RE06.GaussianMoment.finRowStack_gram_submatrix
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.finRowStack_gram_submatrix
#print axioms NLA.Proofs.RE06.GaussianMoment.finRowStack_gram_submatrix
#actual_theorem NLA.Proofs.RE06.GaussianMoment.fin_inverse_gram_first_entry
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.fin_inverse_gram_first_entry
#print axioms NLA.Proofs.RE06.GaussianMoment.fin_inverse_gram_first_entry
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedEntries_hasLaw
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedEntries_hasLaw
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedEntries_hasLaw
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_measurable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_measurable
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_measurable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_norm_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_norm_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_inner_norm_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.joinedGramEntry_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.entryMatrix_measurable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.entryMatrix_measurable
#print axioms NLA.Proofs.RE06.GaussianMoment.entryMatrix_measurable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_measurable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_measurable
#print axioms NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_measurable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_zero_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_zero_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_zero_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_zero_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_zero_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_zero_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.permutedEntries_hasLaw
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.permutedEntries_hasLaw
#print axioms NLA.Proofs.RE06.GaussianMoment.permutedEntries_hasLaw
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_permuted
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_permuted
#print axioms NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_permuted
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.gramInverseEntry_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.trace_inverse_gram_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.trace_inverse_gram_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.trace_inverse_gram_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.trace_inverse_gram_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.trace_inverse_gram_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.trace_inverse_gram_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral
#actual_theorem NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_measurable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_measurable
#print axioms NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_measurable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integrable_of_hasLaw
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integrable_of_hasLaw
#print axioms NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integrable_of_hasLaw
#actual_theorem NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral_of_hasLaw
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral_of_hasLaw
#print axioms NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral_of_hasLaw
#actual_theorem NLA.Proofs.RE06.GaussianMoment.stream_block_pseudoinverse_frobeniusSq_integrable
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.stream_block_pseudoinverse_frobeniusSq_integrable
#print axioms NLA.Proofs.RE06.GaussianMoment.stream_block_pseudoinverse_frobeniusSq_integrable
#actual_theorem NLA.Proofs.RE06.GaussianMoment.stream_block_pseudoinverse_frobeniusSq_integral
#assert_trust kernel NLA.Proofs.RE06.GaussianMoment.stream_block_pseudoinverse_frobeniusSq_integral
#print axioms NLA.Proofs.RE06.GaussianMoment.stream_block_pseudoinverse_frobeniusSq_integral
