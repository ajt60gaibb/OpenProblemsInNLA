/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! MD-03: the complete dimension-independent Komlós signing question.
The reviewed specification is docs/lean/statements/MD-03/NUMERICAL_TARGETS.md.
This defines a proposition and does not claim to prove it. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.MD03

/-- A single positive real constant works for every positive dimension and
every matrix with squared Euclidean column norms at most one. -/
def Target : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m n : ℕ), 0 < m → 0 < n →
      ∀ A : Matrix (Fin m) (Fin n) ℝ,
        (∀ j, ∑ i, (A i j) ^ 2 ≤ 1) →
        ∃ x : Fin n → ℝ,
          (∀ j, x j = -1 ∨ x j = 1) ∧
          ∀ i, |∑ j, A i j * x j| ≤ C

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.MD03
