import NLA.Proofs.RA05.HyperplaneBridge
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
#print axioms NLA.Proofs.RA05.unitHyperplane_projector
#print axioms NLA.Proofs.RA05.rowCost_unitHyperplane
#print axioms NLA.Proofs.RA05.strongCoreset_implies_allVectorEmbedding
#assert_trust kernel NLA.Proofs.RA05.unitHyperplane_projector
#assert_trust kernel NLA.Proofs.RA05.rowCost_unitHyperplane
#assert_trust kernel NLA.Proofs.RA05.strongCoreset_implies_allVectorEmbedding
