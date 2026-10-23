import NLA.Statements.PF05
import Reviewed.PF05

/-! Definitional identity with the separately reviewed frozen boundary. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.PF05

theorem target_eq_reviewed :
    NLA.Statements.PF05.Target = NLA.ReviewedStatements.PF05.Target := rfl

#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed
end NLA.PF05
