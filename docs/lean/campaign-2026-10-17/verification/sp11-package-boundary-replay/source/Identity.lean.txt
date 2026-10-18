import NLA.Statements.SP11
import Reviewed.SP11

/-! Definitional identity with the separately reviewed frozen boundary. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP11

theorem target_eq_reviewed :
    NLA.Statements.SP11.Target = NLA.ReviewedStatements.SP11.Target := rfl

#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed

end NLA.SP11
