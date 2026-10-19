import NLA.Statements.PF05
import Reviewed.PF05

/-! Independent frozen-boundary identity check. These assertions check the
statement's type and trust boundary, not the truth of PF-05. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

#assert_statement NLA.Statements.PF05.Target
#assert_statement NLA.ReviewedStatements.PF05.Target
#assert_trust kernel NLA.Statements.PF05.Target
#assert_trust kernel NLA.ReviewedStatements.PF05.Target

example : NLA.Statements.PF05.Target =
    NLA.ReviewedStatements.PF05.Target := by
  rfl
