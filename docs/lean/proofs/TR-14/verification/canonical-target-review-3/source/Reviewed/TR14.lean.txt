/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-14: equality of ordinary and symmetric exact ranks for all complex
Hankel tensors. See docs/lean/statements/TR-14/NUMERICAL_TARGETS.md.
The all-width equivalence expresses equality of the minimum decomposition
lengths; it includes zero and every exceptional tensor. No proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.TR14

/-- Zero-based sum of tensor indices, with its exact finite bound. -/
def HankelIndex {m n : ℕ} (i : Fin m → Fin n) : Fin (m * (n - 1) + 1) :=
  ⟨∑ k, (i k).val, by
    calc
      (∑ k, (i k).val) ≤ ∑ _k : Fin m, (n - 1) :=
        Finset.sum_le_sum fun k _ => by have := (i k).isLt; omega
      _ = m * (n - 1) := by simp
      _ < m * (n - 1) + 1 := Nat.lt_succ_self _⟩

def Hankel {m n : ℕ} (h : Fin (m * (n - 1) + 1) → ℂ)
    (i : Fin m → Fin n) : ℂ :=
  h (HankelIndex i)

def OrdinaryWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ u : Fin r → Fin m → Fin n → ℂ,
    ∀ i, H i = ∑ j, ∏ k, u j k (i k)

def SymmetricWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ c : Fin r → ℂ, ∃ v : Fin r → Fin n → ℂ,
    ∀ i, H i = ∑ j, c j * ∏ k, v j (i k)

/-- Zero padding makes width `r` equivalent to width at most `r`. Over the
complex numbers both finite decomposition minima exist for Hankel tensors. -/
def Target : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 2 ≤ n →
    ∀ h : Fin (m * (n - 1) + 1) → ℂ, ∀ r : ℕ,
      OrdinaryWidth (Hankel h) r ↔ SymmetricWidth (Hankel h) r

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.TR14
