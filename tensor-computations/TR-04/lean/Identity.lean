import NLA.Statements.TR04
import Reviewed.TR04

/-! Exact identity with the independently frozen complete original Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.TR04

theorem target_eq_reviewed :
    NLA.Statements.TR04.Target=NLA.ReviewedStatements.TR04.Target := rfl

#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed
end NLA.TR04
