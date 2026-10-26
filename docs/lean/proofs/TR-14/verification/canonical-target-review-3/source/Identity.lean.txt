import NLA.Statements.TR14
import Reviewed.TR14

/-! Definitional identity with the separately reviewed frozen boundary. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.TR14

theorem target_eq_reviewed :
    NLA.Statements.TR14.Target = NLA.ReviewedStatements.TR14.Target := rfl

#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed

end NLA.TR14
