import NLA.Computation.ExactRealMachine
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IE-12: a uniform exact-real finite program with an all-draw operation bound
and the original A-only normwise backward error. This states existence; it does
not implement or prove the archived solver. See the approved numerical specification. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Computation.ExactRealMachine

namespace NLA.Statements.IE12

noncomputable def VectorNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- The genuine Euclidean induced norm. In the positive-dimensional target,
the unit-sphere image is nonempty and bounded. -/
noncomputable def SpectralNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : Fin n → ℝ, (∑ i, (x i) ^ 2) = 1 ∧
    y = VectorNorm (fun i => ∑ j, A i j * x j)}

/-- The numerator uses exactly the original A and b. The nonzero output and
norm-one promise in Target ensure a strictly positive denominator. -/
noncomputable def BackwardError {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) : ℝ :=
  VectorNorm (fun i => (∑ j, A i j * x j) - b i) / (SpectralNorm A * VectorNorm x)

/-- Real exponent, with positive epsilon in every quantified input. -/
noncomputable def CostBound (C q : ℝ) (n : ℕ) (epsilon : ℝ) : ℝ :=
  C * (n : ℝ) ^ 2 * Real.rpow epsilon (-q)

/-- One bounded trace of the actual machine returns this actual stored vector.
Zero output and failure cannot satisfy this predicate. -/
def BoundedReturn (P : Program) (C q : ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (epsilon : ℝ)
    (omega : Streams) (x : Fin n → ℝ) : Prop :=
  x ≠ 0 ∧ ∃ t : ℕ, (t : ℝ) ≤ CostBound C q n epsilon ∧
    output P n (run P A b epsilon omega t) = some x

/-- The same runtime/output predicate is used inside and outside the success
event. A program cannot hide unbounded or failed runs in its probability tail. -/
def SuccessEvent (P : Program) (C q : ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (epsilon : ℝ) : Set Streams :=
  {omega | ∃ x : Fin n → ℝ,
    BoundedReturn P C q A b epsilon omega x ∧ BackwardError A b x ≤ epsilon}

/-- One finite program and two absolute positive real constants precede all
dimensions, matrices, RHS vectors, tolerances and random-stream realizations. -/
def Target : Prop :=
  ∃ P : Program, ∃ C q : ℝ, 0 < C ∧ 0 < q ∧
    ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
      A.det ≠ 0 → SpectralNorm A = 1 → ∀ b : Fin n → ℝ, b ≠ 0 →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
        (∀ omega : Streams, ∃ x : Fin n → ℝ, BoundedReturn P C q A b epsilon omega x) ∧
        ENNReal.ofReal (99 / 100 : ℝ) ≤ StreamLaw (SuccessEvent P C q A b epsilon)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.IE12
