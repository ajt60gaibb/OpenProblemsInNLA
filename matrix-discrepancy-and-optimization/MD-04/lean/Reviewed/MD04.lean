/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Real.Sqrt
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! MD-04: the complete Beck–Fiala square-root sparsity question.
The reviewed specification is docs/lean/statements/MD-04/NUMERICAL_TARGETS.md.
This defines a proposition and does not claim to prove it. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.MD04

/-- Every column of an incidence matrix receives a sign; the same positive
constant bounds every row for every allowed dimension and sparsity. -/
def Target : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m n t : ℕ), 0 < m → 0 < n → 1 ≤ t → t ≤ m →
      ∀ A : Matrix (Fin m) (Fin n) ℝ,
        (∀ i j, A i j = 0 ∨ A i j = 1) →
        (∀ j, ∑ i, A i j ≤ (t : ℝ)) →
        ∃ x : Fin n → ℝ,
          (∀ j, x j = -1 ∨ x j = 1) ∧
          ∀ i, |∑ j, A i j * x j| ≤ C * Real.sqrt (t : ℝ)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.MD04
