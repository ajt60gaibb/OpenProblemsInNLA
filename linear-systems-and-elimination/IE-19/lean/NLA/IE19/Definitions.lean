/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to IE-19.
This file is the proof-independent statement boundary. No local theorem is imported.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

open scoped NNReal
noncomputable section

namespace NLA.IE19

/-- The comparison matrix `α I + m 11ᵀ`; the inequalities in IE-19 are entrywise. -/
def comparisonMatrix {n : ℕ} (α m : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then α else 0) + m

/-- The exact maximum absolute row-sum norm. The finite supremum is taken in `ℝ≥0`
before coercing to `ℝ`; it is zero for an empty matrix. This is not the default
entrywise supremum norm on a matrix. -/
noncomputable def rowSumNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((Finset.univ.sup fun i : Fin n => ∑ j : Fin n, ‖M i j‖₊) : ℝ≥0)

/-- Symmetry, strictly positive entries bounded by the comparison matrix, and
weak diagonal dominance, exactly as in the canonical IE-19 statement. -/
def Admissible {n : ℕ} (α m : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  J.transpose = J ∧
  (∀ i j, 0 < J i j ∧ J i j ≤ comparisonMatrix α m i j) ∧
  (∀ i, (∑ j ∈ Finset.univ.erase i, J i j) ≤ J i i)

/-- The displayed proposed lower bound, with all arithmetic over the reals. -/
def comparisonBound (n : ℕ) (α m : ℝ) : ℝ :=
  (α + 2 * m * ((n : ℝ) - 1)) / (α * (α + m * (n : ℝ)))

/-- The inequality part of the original universal conjecture. -/
def LowerBoundConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ α m : ℝ, 0 < m → ((n : ℝ) - 2) * m ≤ α →
    ∀ J : Matrix (Fin n) (Fin n) ℝ,
      Admissible α m J → comparisonBound n α m ≤ rowSumNorm J⁻¹

/-- The full canonical conjecture, including its equality characterization.
No extra invertibility or strict-dominance assumption has been inserted. -/
def SharpConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ α m : ℝ, 0 < m → ((n : ℝ) - 2) * m ≤ α →
    ∀ J : Matrix (Fin n) (Fin n) ℝ, Admissible α m J →
      comparisonBound n α m ≤ rowSumNorm J⁻¹ ∧
      (rowSumNorm J⁻¹ = comparisonBound n α m ↔ J = comparisonMatrix α m)

/-- Colbrook's order-three counterexample: diagonal `2`, off-diagonal `1/2`. -/
def witness : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 1/2, 1/2; 1/2, 2, 1/2; 1/2, 1/2, 2]

/-- Rational candidate inverse, to be proved to equal the actual matrix inverse. -/
def witnessInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![5/9, -1/9, -1/9; -1/9, 5/9, -1/9; -1/9, -1/9, 5/9]

/-- Rational candidate inverse of the comparison matrix at `α=m=1`. -/
def comparisonInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3/4, -1/4, -1/4; -1/4, 3/4, -1/4; -1/4, -1/4, 3/4]

end NLA.IE19
