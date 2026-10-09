/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Computation.BandIntervals
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IV-04: the original polynomial binary-time exact solution-hull question.
Complete independently reviewed specification:
docs/lean/statements/IV-04/NUMERICAL_TARGETS.md.
Empty sets, infinite endpoints and disconnected projections are included.
No unconditional solver or P=NP classification is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Computation NLA.Computation.BandIntervals

namespace NLA.ReviewedStatements.IV04

/-- A single concrete deterministic machine returns the exact hull in uniform
polynomial binary time, with no regularity promise on any interval family. -/
def Target : Prop :=
  ∃ M : FiniteMachine, ∃ p : PolynomialBound,
    ∀ a : SystemInput, 1 ≤ a.band.n → a.Ordered →
      ∃ output : HullOutput a.band.n,
        M.RunsWithin (encodeSystem a) (encodeHull output)
          (p.atLength (encodeSystem a).length) ∧
        CorrectHull a output

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.IV04
