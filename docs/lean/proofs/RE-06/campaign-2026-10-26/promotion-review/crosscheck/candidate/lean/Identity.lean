import NLA.Statements.RE06
import Reviewed.RE06
import Solution
set_option leancert.trust "kernel"
theorem re06_original_reviewed_identity : NLA.Statements.RE06.Target =
  NLA.ReviewedStatements.RE06.Target := rfl
#assert_trust kernel re06_original_reviewed_identity
