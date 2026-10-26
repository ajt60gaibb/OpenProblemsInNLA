import FullSolution
import Identity
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace IndependentCanonicalIdentityGeometry

theorem literal_reviewed_identity :
    NLA.Statements.TR04.Target=NLA.ReviewedStatements.TR04.Target := rfl

theorem actual_proof_at_reviewed_target : NLA.ReviewedStatements.TR04.Target :=
  NLA.TR04.target

#assert_trust kernel NLA.TR04.target_eq_reviewed
#assert_trust kernel literal_reviewed_identity
#assert_trust kernel actual_proof_at_reviewed_target
#print axioms NLA.TR04.target_eq_reviewed
#print axioms literal_reviewed_identity
#print axioms actual_proof_at_reviewed_target
end IndependentCanonicalIdentityGeometry
