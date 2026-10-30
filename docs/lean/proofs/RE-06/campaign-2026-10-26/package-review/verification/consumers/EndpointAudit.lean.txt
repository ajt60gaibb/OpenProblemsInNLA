import NLA.Proofs.RE06.FullTargetAudit

set_option leancert.trust "kernel"

#re06_theorem NLA.Proofs.RE06.svd_total
#assert_trust kernel NLA.Proofs.RE06.svd_total
#print axioms NLA.Proofs.RE06.svd_total

#re06_theorem NLA.Proofs.RE06.query_bound
#assert_trust kernel NLA.Proofs.RE06.query_bound
#print axioms NLA.Proofs.RE06.query_bound

#re06_theorem NLA.Proofs.RE06.successful
#assert_trust kernel NLA.Proofs.RE06.successful
#print axioms NLA.Proofs.RE06.successful

#re06_theorem NLA.Proofs.RE06.original_claim
#assert_trust kernel NLA.Proofs.RE06.original_claim
#print axioms NLA.Proofs.RE06.original_claim

#re06_theorem NLA.Proofs.RE06.explicit_claim
#assert_trust kernel NLA.Proofs.RE06.explicit_claim
#print axioms NLA.Proofs.RE06.explicit_claim

#re06_theorem NLA.Proofs.RE06.target
#assert_trust kernel NLA.Proofs.RE06.target
#print axioms NLA.Proofs.RE06.target
