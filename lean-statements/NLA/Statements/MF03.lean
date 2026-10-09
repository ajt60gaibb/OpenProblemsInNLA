import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Coprime.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! MF-03: the all-order complex disk bound for the diagonal Pade approximant
to the entire series with coefficients 1/(2j)!. The specification is
docs/lean/statements/MF-03/NUMERICAL_TARGETS.md. No target proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Statements.MF03

/-- Exact normalized diagonal Pade coefficient conditions. The finite
convolution enforces vanishing of Q f - P through degree 2m inclusive. -/
def NormalizedPadeRepresentation (m : ℕ) (P Q : Polynomial ℂ) : Prop :=
  P.natDegree ≤ m ∧ Q.natDegree ≤ m ∧ Q.eval 0 = 1 ∧
    ∀ j : ℕ, j ≤ 2 * m →
      (∑ i ∈ Finset.range (j + 1),
        Q.coeff i / ((2 * (j - i)).factorial : ℂ)) = P.coeff j

/-- Coprimeness removes all removable factors before testing for poles. -/
def ReducedPadeRepresentation (m : ℕ) (P Q : Polynomial ℂ) : Prop :=
  NormalizedPadeRepresentation m P Q ∧ IsCoprime P Q

/-- Existence excludes a vacuous bound. Every reduced representative of the
same rational approximant has no pole and satisfies the weak bound on the
entire closed complex disk, for every positive order. -/
def Target : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∃ P Q : Polynomial ℂ, ReducedPadeRepresentation m P Q) ∧
      ∀ P Q : Polynomial ℂ, ReducedPadeRepresentation m P Q →
        ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
          Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.MF03
