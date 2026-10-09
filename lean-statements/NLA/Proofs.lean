import NLA.Proofs.RA06.GraphSupportCount
import NLA.Proofs.RA06.GraphSampling
import NLA.Proofs.RA06.Bernoulli
import NLA.Proofs.RA06.GraphFinite
import NLA.Proofs.RA06.Asymptotic
import NLA.Proofs.RA06.Final

/-!
Build and kernel-audit the reviewed RA-06 lemmas and the theorem inhabiting the
frozen original `NLA.Statements.RA06.Target`.
-/

set_option leancert.trust "kernel"

#assert_trust kernel NLA.Proofs.RA06.graphMatrix_fullColumnRank
#assert_trust kernel NLA.Proofs.RA06.graphMatrix_inputEnergy
#assert_trust kernel NLA.Proofs.RA06.graphMatrix_totalSensitivity_bound
#assert_trust kernel NLA.Proofs.RA06.embedding_to_weighted
#assert_trust kernel NLA.Proofs.RA06.sample_positiveEdgeCount_eq_retainedCount
#assert_trust kernel NLA.Proofs.RA06.positiveEdgeCount_lower_of_all_degrees
#assert_trust kernel NLA.Proofs.RA06.expectedSize_eq_sum_count
#assert_trust kernel NLA.Proofs.RA06.expectedSize_lower_of_success_count_bound
#assert_trust kernel NLA.Proofs.RA06.supportDegree_lower_of_approx
#assert_trust kernel NLA.Proofs.RA06.successful_retainedCount_lower
#assert_trust kernel NLA.Proofs.RA06.expectedSize_lower_from_graph_success
#assert_trust kernel NLA.Proofs.RA06.exists_large_accuracy_parameter_for_coefficients
#assert_trust kernel NLA.Proofs.RA06.finite_bounds_contradict_for_coefficients
#assert_trust kernel NLA.Proofs.RA06.budget_log_upper_for_ceiling_card_bound
#assert_trust kernel NLA.Proofs.RA06.target
