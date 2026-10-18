import NLA.Statements.SP12
import Reviewed.SP12

/-! Definitional identity with the separately reviewed frozen boundary. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP12

theorem target_eq_reviewed :
    NLA.Statements.SP12.Target = NLA.ReviewedStatements.SP12.Target := rfl

#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed

end NLA.SP12
