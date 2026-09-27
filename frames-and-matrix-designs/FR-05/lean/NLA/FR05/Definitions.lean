/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The deterministic statement layer for FR-05. The public predicate below is the
original all-signals, entrywise-modulus definition; it does not quotient vectors
by phase or replace the measurement model by a rank condition.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

/-- Complex signals in ambient dimension `d`. -/
abbrev Signal (d : ℕ) := Fin d → ℂ

/-- An `m`-row complex phase-retrieval measurement frame. -/
abbrev Frame (m d : ℕ) := Matrix (Fin m) (Fin d) ℂ

/-- The modulus of the `i`-th complex linear measurement of `x`. -/
def rowMagnitude {m d : ℕ} (A : Frame m d) (x : Signal d) (i : Fin m) : ℝ :=
  ‖∑ j, A i j * x j‖

/-- Equality of all componentwise measurement moduli. -/
def SameMeasurements {m d : ℕ} (A : Frame m d) (x y : Signal d) : Prop :=
  ∀ i, rowMagnitude A x i = rowMagnitude A y i

/-- The original global-phase relation, written using `exp (θ i)`. -/
def GloballyPhased {d : ℕ} (x y : Signal d) : Prop :=
  ∃ θ : ℝ, y = (Complex.exp (θ * Complex.I)) • x

/-- Injectivity of the original phase-retrieval map on every pair of signals. -/
def PhaseRetrievalInjective {m d : ℕ} (A : Frame m d) : Prop :=
  ∀ x y : Signal d, SameMeasurements A x y → GloballyPhased x y

/-- The first coordinate, available in every dimension at least two. -/
def firstCoordinate (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨0, by lia⟩

/-- The second coordinate, available in every dimension at least two. -/
def secondCoordinate (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨1, by lia⟩

/-- A standard coordinate vector. -/
def standardBasis {d : ℕ} (j : Fin d) : Signal d :=
  fun k => if k = j then 1 else 0

/-- The rank-two Hermitian seed in Li's construction: `diag(1,-1,0,...)`. -/
def qZero (d : ℕ) (hd : 2 ≤ d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun k =>
    if k = firstCoordinate d hd then 1
    else if k = secondCoordinate d hd then -1
    else 0

/-- The actual Hermitian quadratic form associated to a complex matrix. -/
def quadraticForm {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (x : Signal d) : ℂ :=
  star x ⬝ᵥ Q *ᵥ x

/-- The conjugated column corresponding to a row of a measurement frame.
For `a = conjugateRow A i`, the scalar `star a ⬝ᵥ x` is precisely the
complex linear measurement in row `i`. -/
def conjugateRow {m d : ℕ} (A : Frame m d) (i : Fin m) : Signal d :=
  star (A i)

/-- The Hermitian difference `xxᴴ - yyᴴ`.  A zero quadratic form for this
matrix says that the corresponding two measurement magnitudes agree. -/
def rankOneDifference {d : ℕ} (x y : Signal d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec x (star x) - Matrix.vecMulVec y (star y)

/-- A simple all-ones frame used only to certify the exact ambiguity bridge.
It has the same row count as FR-05 but is not the random or locally regular
frame from the manuscript. -/
def flatFrame (m d : ℕ) : Frame m d := fun _ _ => 1

end NLA.FR05
