/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Statements.KrylovCompression
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IE-10: conditioning of the exact complex-sphere cyclic Krylov compression.
The complete approved specification is docs/lean/statements/IE-10/NUMERICAL_TARGETS.md.
The proposition is defined, not proved. Both live and frozen targets import
the same reviewed concrete helper definitions, including Gram–Schmidt. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.KrylovCompression

namespace NLA.ReviewedStatements.IE10

/-- The same positive real constants work for every allowed dimension and width. -/
def Target : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ n k : ℕ, 3 ≤ n → 2 ≤ k → k < n →
      ENNReal.ofReal ((99 : ℝ) / 100) ≤
        GaussianLaw n {z | CompressionCondition k z ≤ ENNReal.ofReal (C * (n : ℝ) ^ c)}

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.IE10
