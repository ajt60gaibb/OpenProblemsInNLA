import NLA.Statements.TR14
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Instances.Complex
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-13: all five ranks on a nonempty Zariski-open set of odd-order complex
Hankel tensors. Exact specification: docs/lean/statements/TR-13/NUMERICAL_TARGETS.md.
No generic-rank theorem or target proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open Filter
open NLA.Statements.TR14

namespace NLA.Statements.TR13

/-- The full homogeneous rational normal curve, including a=0 or b=0. -/
def VandermondeVector (n : ℕ) (a b : ℂ) (i : Fin n) : ℂ :=
  a ^ (n - 1 - i.val) * b ^ i.val

/-- Coefficients may vanish, but each projective parameter pair is nonzero. -/
def VandermondeWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ c a b : Fin r → ℂ,
    (∀ j, a j ≠ 0 ∨ b j ≠ 0) ∧
    ∀ i, H i = ∑ j, c j * ∏ k, VandermondeVector n (a j) (b j) (i k)

/-- Ordinary approximants are arbitrary complex tensors, without Hankel or
symmetry constraints. Convergence is entrywise in the usual complex topology. -/
def OrdinaryBorderWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ T : ℕ → ((Fin m → Fin n) → ℂ),
    (∀ l, OrdinaryWidth (T l) r) ∧
    ∀ i, Tendsto (fun l => T l i) atTop (nhds (H i))

/-- Symmetric approximants remain symmetric, but need not be Hankel. -/
def SymmetricBorderWidth {m n : ℕ} (H : (Fin m → Fin n) → ℂ) (r : ℕ) : Prop :=
  ∃ T : ℕ → ((Fin m → Fin n) → ℂ),
    (∀ l, SymmetricWidth (T l) r) ∧
    ∀ i, Tendsto (fun l => T l i) atTop (nhds (H i))

/-- Padding makes width-r equivalent to rank at most r, including r=0. -/
def EqualFiveRanks {m n : ℕ} (H : (Fin m → Fin n) → ℂ) : Prop :=
  ∀ r : ℕ,
    (OrdinaryWidth H r ↔ SymmetricWidth H r) ∧
    (OrdinaryWidth H r ↔ OrdinaryBorderWidth H r) ∧
    (OrdinaryWidth H r ↔ SymmetricBorderWidth H r) ∧
    (OrdinaryWidth H r ↔ VandermondeWidth H r)

/-- A witnessed principal open is nonempty and Zariski-open; every nonempty
affine Zariski-open contains one. No genericity oracle or predefined open is used. -/
def Target : Prop :=
  ∀ m n : ℕ, 5 ≤ m → Odd m → 2 ≤ n →
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ,
      (∃ h : Fin (m * (n - 1) + 1) → ℂ, MvPolynomial.eval h p ≠ 0) ∧
      ∀ h : Fin (m * (n - 1) + 1) → ℂ,
        MvPolynomial.eval h p ≠ 0 → EqualFiveRanks (Hankel h)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.TR13
