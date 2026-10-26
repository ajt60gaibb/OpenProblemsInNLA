import NLA.Statements.TR06
import Reviewed.TR06

/-! Exact identity with the separately reviewed intrinsic statement boundary. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.TR06
theorem target_eq_reviewed :
    NLA.Statements.TR06.Target = NLA.ReviewedStatements.TR06.Target := rfl
#assert_trust kernel target_eq_reviewed
#print axioms target_eq_reviewed
end NLA.TR06
