import NLA.Proofs.TR14.Final
set_option leancert.trust "kernel"
#assert_trust kernel NLA.Proofs.TR14.ordinary_lower_of_minimal_monic_succ
#assert_trust kernel NLA.Proofs.TR14.ordinary_lower_of_minimal_monic
#assert_trust kernel NLA.Proofs.TR14.ordinaryWidth_to_symmetricWidth
#assert_trust kernel NLA.Proofs.TR14.target
#print axioms NLA.Proofs.TR14.ordinary_lower_of_minimal_monic_succ
#print axioms NLA.Proofs.TR14.ordinary_lower_of_minimal_monic
#print axioms NLA.Proofs.TR14.ordinaryWidth_to_symmetricWidth
#print axioms NLA.Proofs.TR14.target
example : NLA.Statements.TR14.Target := NLA.Proofs.TR14.target
