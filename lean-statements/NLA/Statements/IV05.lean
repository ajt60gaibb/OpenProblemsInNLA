import NLA.Computation.FiniteMachine
import NLA.Computation.BinaryEncoding
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IV-05: polynomial binary-time exact coordinate hull under the full
inverse-M interval promise. Exact specification:
docs/lean/statements/IV-05/NUMERICAL_TARGETS.md.
This defines the transducer-existence proposition, not a hull algorithm. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Computation NLA.Computation.BinaryEncoding

namespace NLA.Statements.IV05

/-- The input endpoints are ordered entrywise, without strict widths. -/
def OrderedInput (a : IntervalInput) : Prop :=
  (∀ i j, a.lowerMatrix i j ≤ a.upperMatrix i j) ∧
  (∀ i, a.lowerRhs i ≤ a.upperRhs i)

/-- Every real entry varies independently between its rational endpoints. -/
def InMatrixInterval (a : IntervalInput)
    (A : Matrix (Fin a.n) (Fin a.n) ℝ) : Prop :=
  ∀ i j, (a.lowerMatrix i j : ℝ) ≤ A i j ∧ A i j ≤ (a.upperMatrix i j : ℝ)

def InRhsInterval (a : IntervalInput) (b : Fin a.n → ℝ) : Prop :=
  ∀ i, (a.lowerRhs i : ℝ) ≤ b i ∧ b i ≤ (a.upperRhs i : ℝ)

/-- The canonical definition: invertible, nonpositive off-diagonal entries,
and entrywise nonnegative genuine inverse. Zero off-diagonal entries are allowed. -/
def NonsingularMMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  B.det ≠ 0 ∧
  (∀ i j, i ≠ j → B i j ≤ 0) ∧
  (∀ i j, 0 ≤ B⁻¹ i j)

/-- Guard both inverse uses explicitly rather than relying on a totalized inverse. -/
def InverseMMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.det ≠ 0 ∧ NonsingularMMatrix A⁻¹

def InputPromise (a : IntervalInput) : Prop :=
  1 ≤ a.n ∧ OrderedInput a ∧
  ∀ A : Matrix (Fin a.n) (Fin a.n) ℝ, InMatrixInterval a A → InverseMMatrix A

/-- Under the promise this is exactly x=A inverse b, with A and b chosen
independently from their full real entry intervals. -/
def IsSolution (a : IntervalInput) (x : Fin a.n → ℝ) : Prop :=
  ∃ A : Matrix (Fin a.n) (Fin a.n) ℝ, ∃ b : Fin a.n → ℝ,
    InMatrixInterval a A ∧ InRhsInterval a b ∧
    ∀ i, (∑ j, A i j * x j) = b i

/-- Enclosure and separate attainment of both endpoints at every coordinate.
The witnesses may differ across coordinates and between the two endpoints. -/
def ExactHull (a : IntervalInput) (lower upper : Fin a.n → ℚ) : Prop :=
  ∀ i,
    (∀ x : Fin a.n → ℝ, IsSolution a x →
      (lower i : ℝ) ≤ x i ∧ x i ≤ (upper i : ℝ)) ∧
    (∃ x : Fin a.n → ℝ, IsSolution a x ∧ x i = (lower i : ℝ)) ∧
    (∃ x : Fin a.n → ℝ, IsSolution a x ∧ x i = (upper i : ℝ))

/-- The complete exact-output target in actual binary machine steps.
The output includes its dimension and every rational endpoint bit.
There is no condition on behavior outside InputPromise. -/
def Target : Prop :=
  ∃ M : FiniteMachine, ∃ p : PolynomialBound,
    ∀ a : IntervalInput, InputPromise a →
      ∃ lower upper : Fin a.n → ℚ,
        M.RunsWithin (encodeInterval a)
          (encodeIntervalOutput ⟨a.n, lower, upper⟩)
          (p.atLength (encodeInterval a).length) ∧
        ExactHull a lower upper

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.IV05
