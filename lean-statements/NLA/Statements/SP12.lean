import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! SP-12: the full chromatic lower bound for PSD nullity with SAP.
See docs/lean/statements/SP-12/NUMERICAL_TARGETS.md. No proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Statements.SP12

def HasPattern {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧
  ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j)

/-- The usual nonnegative real quadratic form; symmetry is required separately. -/
def NonnegativeQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * A i j * x j

/-- Ordinary multiplication, entrywise multiplication, and zero diagonal are
the three distinct constraints in the original strong Arnold property. -/
def StrongArnold {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, X i j = X j i) →
    A * X = 0 → (∀ i j, A i j * X i j = 0) →
    (∀ i, X i i = 0) → X = 0

/-- The least number of colors in a proper coloring. The defining set contains
`n` via the identity coloring, so no empty-infimum convention enters the target. -/
noncomputable def ChromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c : ℕ | ∃ f : Fin n → Fin c, ∀ i j, G.Adj i j → f i ≠ f j}

/-- The explicit witness formulation of `ν(G) ≥ χ(G)-1`. -/
def Target : Prop :=
  ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      HasPattern G A ∧ NonnegativeQuadraticForm A ∧ StrongArnold A ∧
      ChromaticNumber G - 1 ≤ n - A.rank

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.SP12
