/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Statements.Shared.TR17Geometry
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-17: Frobenius minimality for Euclidean distance degree of every
admissible Segre–Veronese cone, for every positive definite real metric.
The complete original problem and reviewed exact specification are retained
under `docs/lean/statements/TR-17/`. This declares the statement, not a proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.ReviewedStatements.TR17

/-- The generic critical-scheme length, including algebraic multiplicity,
for every positive definite metric is at least the repeated-entry-weighted
Frobenius value. -/
def Target : Prop := NLA.Statements.Shared.TR17Geometry.Claim

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.TR17
