import NLA.Statements.RA10
import Reviewed.RA10
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

/- This is the exact frozen statement, not a reconstructed or conditional variant. -/
theorem NLA.RA10.statement_identity :
    NLA.Statements.RA10.Target = NLA.ReviewedStatements.RA10.Target := by
  rfl

#assert_trust kernel NLA.RA10.statement_identity
#print axioms NLA.RA10.statement_identity
