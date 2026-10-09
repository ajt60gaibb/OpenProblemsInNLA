/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! PF-04: the full order-six maximum-cp-rank question, including sharpness.
The reviewed specification is docs/lean/statements/PF-04/NUMERICAL_TARGETS.md.
This defines a proposition and does not claim to prove it. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.PF04

/-- Exact entrywise-nonnegative real Gram factorization of width `r`.
Width zero is allowed and represents exactly the zero matrix. -/
def HasFactor (A : Matrix (Fin 6) (Fin 6) ℝ) (r : ℕ) : Prop :=
  ∃ B : Matrix (Fin 6) (Fin r) ℝ,
    (∀ i k, 0 ≤ B i k) ∧
    ∀ i j, A i j = ∑ k, B i k * B j k

/-- Complete positivity uses an actual finite nonnegative factor. -/
def CompletelyPositive (A : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  ∃ r : ℕ, HasFactor A r

/-- Every CP matrix of order six admits nine columns (possibly zero),
and some such matrix admits no factor with fewer columns. -/
def Target : Prop :=
  (∀ A : Matrix (Fin 6) (Fin 6) ℝ,
    CompletelyPositive A → HasFactor A 9) ∧
  ∃ A : Matrix (Fin 6) (Fin 6) ℝ,
    CompletelyPositive A ∧ ∀ r : ℕ, r < 9 → ¬ HasFactor A r

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.PF04
