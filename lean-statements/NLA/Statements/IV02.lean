import NLA.Computation.BandIntervals
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IV-02: the original polynomial binary-time exact determinant-range question.
Complete independently reviewed specification:
docs/lean/statements/IV-02/NUMERICAL_TARGETS.md.
This defines algorithm existence; it does not assert an unconditional solver
or replace the original question by its separate P=NP classification. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Computation NLA.Computation.BandIntervals

namespace NLA.Statements.IV02

/-- One finite machine and one polynomial precede every valid dimension and
input. Both exact rational extrema must be output in an actual bounded run. -/
def Target : Prop :=
  ∃ M : FiniteMachine, ∃ p : PolynomialBound,
    ∀ a : BandInput, 2 ≤ a.n → a.Ordered →
      ∃ dlo dhi : ℚ,
        M.RunsWithin (encodeBand a) (encodeRange dlo dhi)
          (p.atLength (encodeBand a).length) ∧
        CorrectRange a dlo dhi

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.IV02
