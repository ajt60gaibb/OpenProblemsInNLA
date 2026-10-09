import NLA.Computation.FiniteMachine
import NLA.Computation.BinaryEncoding
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! AV-01: polynomial binary-time decision of exactly 2^n real solutions.
The full specification is docs/lean/statements/AV-01/NUMERICAL_TARGETS.md.
This defines the affirmative complexity proposition; no solver is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Computation NLA.Computation.BinaryEncoding

namespace NLA.Statements.AV01

/-- Exact rational embeddings and componentwise absolute values. -/
def IsSolution (a : AVInput) (x : Fin a.n → ℝ) : Prop :=
  ∀ i, (∑ j, (a.matrix i j : ℝ) * x j) + |x i| = (a.rhs i : ℝ)

/-- A bijection with the entire solution subtype asserts both finiteness
and exactly 2^n distinct real points. Infinite solution sets are negative. -/
def HasExactSolutionCount (a : AVInput) : Prop :=
  Nonempty (Fin (2 ^ a.n) ≃ {x : Fin a.n → ℝ // IsSolution a x})

/-- One fixed finite machine and polynomial bound precede every input.
The output is one actual tape bit and no analytic input promise is imposed. -/
def Target : Prop :=
  ∃ M : FiniteMachine, ∃ p : PolynomialBound,
    ∀ a : AVInput, 1 ≤ a.n →
      ∃ answer : Bool,
        M.DecidesWithin (encodeAV a) answer (p.atLength (encodeAV a).length) ∧
        (answer = true ↔ HasExactSolutionCount a)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.AV01
