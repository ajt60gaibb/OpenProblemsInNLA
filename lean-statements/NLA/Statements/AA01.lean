import NLA.Computation.RoundedTree
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! AA-01: the original always-halting integer-polynomial decision question.
Concrete finite trees, error semantics and encoding are in RoundedTree.
No polynomial running-time bound or evaluator-existence oracle is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Computation NLA.Computation.RoundedTree

namespace NLA.Statements.AA01

/-- One ordinary finite binary machine decides whether a genuine finite
rounded tree exists. Its finite halting-time witness follows each input. -/
def Target : Prop :=
  ∃ M : FiniteMachine,
    ∀ a : PolynomialInput, ValidInput a →
      ∃ answer : Bool, ∃ T : ℕ,
        M.DecidesWithin (encodePolynomial a) answer T ∧
        (answer = true ↔ AccuratelyEvaluable a)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.AA01
