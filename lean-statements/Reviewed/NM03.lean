/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Statements.NMFDecision
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! NM-03: exact rational-input nonnegative rank-two approximation is NP-hard
under actual polynomial binary-time many-one reductions. The original P
alternative is separately named, without asserting its negation.
Exact specification: docs/lean/statements/NM-03/NUMERICAL_TARGETS.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.ReviewedStatements.NM03

open NLA.Computation NLA.Statements.NMFDecision

/-- The original polynomial-solvability alternative, without a separation claim. -/
def PolynomialSolvability : Prop := Complexity.InP DecisionLanguage

/-- All NP languages reduce by actual finite transducer runs with one uniform
polynomial bound. No promise oracle or assumed reduction-cost function is used. -/
def Target : Prop := Complexity.ManyOneNPHard DecisionLanguage

#assert_statement PolynomialSolvability
#assert_statement Target
#assert_trust kernel PolynomialSolvability
#assert_trust kernel Target
#print axioms PolynomialSolvability
#print axioms Target

end NLA.ReviewedStatements.NM03
