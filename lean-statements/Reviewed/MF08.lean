/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Statements.Shared.MF08Decision
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! MF-08: unrestricted static output-feedback stabilization for rational
plants is NP-hard under polynomial binary-time many-one reductions. The
complete canonical problem and approved exact specification are retained
under docs/lean/statements/MF-08/. This declares a statement, not its proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.ReviewedStatements.MF08

open NLA.Statements.Shared.MF08Decision

/-- Polynomial-time many-one NP-hardness in the concrete finite-machine
binary model. -/
def Target : Prop := NLA.Computation.Complexity.ManyOneNPHard DecisionLanguage

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.MF08
