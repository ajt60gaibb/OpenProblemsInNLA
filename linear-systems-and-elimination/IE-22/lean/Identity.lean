import NLA.Statements.IE22
import Reviewed.IE22

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.IE22
theorem target_eq_reviewed :
    NLA.Statements.IE22.Target = NLA.ReviewedStatements.IE22.Target := rfl
#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed
end NLA.Proofs.IE22
