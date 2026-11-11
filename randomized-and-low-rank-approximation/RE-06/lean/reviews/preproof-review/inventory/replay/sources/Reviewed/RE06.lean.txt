/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Computation.NonadaptiveMatrixQuery
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RE-06: the original existential and source's explicit 4,000,000-query
nonadaptive finite-family matrix approximation theorem. The complete
operational exact-real algorithm is in the imported shared module. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Computation.NonadaptiveMatrixQuery

namespace NLA.ReviewedStatements.RE06

/-- Original RE-06 quantifier order for this one concrete uniform algorithm.
The constant and nonnegative integer log exponent precede all inputs. -/
def OriginalClaim : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ b : ℕ,
    ∀ (n m : ℕ), 0 < n →
      ∀ F : Family n m, Function.Injective F →
        ∀ A : Matrix (Fin n) (Fin n) ℝ,
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
            QueryBound n m ε C b ∧ Successful F A ε

/-- The source's explicit stronger numerical theorem: `b=0` and exactly
4,000,000 times the square-root logarithm, with a worst-case query bound. -/
def ExplicitClaim : Prop :=
  ∀ (n m : ℕ), 0 < n →
    ∀ F : Family n m, Function.Injective F →
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          QueryBound n m ε 4000000 0 ∧ Successful F A ε

/-- Full original existential and the resolved explicit companion. -/
def Target : Prop := SVDTotal ∧ OriginalClaim ∧ ExplicitClaim

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.RE06
