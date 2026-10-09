/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Statements.RowDeletion
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IE-22: exact eventual uniform upper constant and no-smaller optimality.
See docs/lean/statements/IE-22/NUMERICAL_TARGETS.md. No target proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RowDeletion

namespace NLA.ReviewedStatements.IE22

/-- On positive dimensions this is the genuine nonempty bounded matrix
supremum, using every real matrix with unit Euclidean rows. -/
noncomputable def Extremum (θ : ℝ) (m n : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A ∧
    y = Real.sqrt ((n : ℝ) / (m : ℝ)) * Real.sqrt (SubsingularSquared θ A)}

/-- Thresholds follow epsilon but precede all matrix dimensions. Positive n
makes the natural inequality R*n≤m exactly the original ratio condition. -/
def UniformUpper (θ c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N R : ℕ,
    ∀ n m : ℕ, 0 < n → 0 < m → N ≤ n → R * n ≤ m →
      Extremum θ m n ≤ c + ε

/-- Both canonical clauses, without the old scaffold's unsupported extension
that dropped n→infinity from a separate supremum-convergence claim. -/
def Target : Prop :=
  ∀ θ a : ℝ, 0 < θ → θ < 1 → 0 < a → GaussianQuantile θ a →
    UniformUpper θ (Real.sqrt (TrimmedMoment a)) ∧
    ∀ c' : ℝ, c' < Real.sqrt (TrimmedMoment a) → ¬ UniformUpper θ c'

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.IE22
