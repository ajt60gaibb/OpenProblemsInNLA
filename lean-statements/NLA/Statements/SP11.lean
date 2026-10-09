import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! SP-11: the original unrestricted real symmetric delta conjecture.
See docs/lean/statements/SP-11/NUMERICAL_TARGETS.md. No proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Statements.SP11

/-- Symmetry, the exact off-diagonal graph pattern, and unrestricted diagonal. -/
def HasPattern {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧
  ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j)

/-- Classical decidability is used only to compute finite neighbor cardinalities. -/
noncomputable def MinimumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact G.minDegree

/-- Real matrix rank-nullity identifies `n - A.rank` with the kernel dimension. -/
def Target : Prop :=
  ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      HasPattern G A ∧ MinimumDegree G ≤ n - A.rank

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.SP11
