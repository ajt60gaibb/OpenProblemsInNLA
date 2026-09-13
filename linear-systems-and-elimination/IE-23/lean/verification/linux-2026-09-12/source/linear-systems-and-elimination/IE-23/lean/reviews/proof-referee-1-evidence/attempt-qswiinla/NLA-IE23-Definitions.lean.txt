/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of IE-23 using Matthew J. Colbrook's induced-norm counterexample.
The underlying rational matrix is attributed to Dokmanić and Gribonval,
Example 4.1; neither that example nor the analytic resolution is claimed here
as new. See SOURCE_CORRESPONDENCE.md.

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section

namespace NLA.IE23

abbrev Vec (n : ℕ) := Fin n → ℂ
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

/-- The genuine complex Euclidean norm, rather than the default supremum
norm on a function space. -/
def euclideanNorm {n : ℕ} (y : Vec n) : ℝ :=
  ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖

/-- The original finite-real-p denominator, defined by the displayed sum and
real power. The canonical conjecture uses only 2 < p, so neither p=2 nor an
infinite-p endpoint is silently included. Positivity for nonzero vectors is a
theorem obligation, not a premise added to the conjecture. -/
def lpNorm {n : ℕ} (p : ℝ) (y : Vec n) : ℝ :=
  (∑ i, ‖y i‖ ^ p) ^ (1 / p)

/-- Every actual ratio from a nonzero right-hand side. Matrix multiplication
acts on the input vector before taking its Euclidean norm. -/
def ratioSet {m n : ℕ} (p : ℝ) (X : Mat n m) : Set ℝ :=
  {r | ∃ y : Vec m, y ≠ 0 ∧ r = euclideanNorm (X.mulVec y) / lpNorm p y}

/-- The genuine supremum in the canonical definition. Generic nonemptiness,
boundedness, and the least-upper-bound property must all be proved on the
original domain; no default value of a conditional supremum is used as a
counterexample. -/
def inducedNorm {m n : ℕ} (p : ℝ) (X : Mat n m) : ℝ := sSup (ratioSet p X)

/-- Actual matrix rank, equal to the dimension of the complex linear range. -/
def FullRowRank {m n : ℕ} (A : Mat m n) : Prop := A.rank = m

/-- The Moore-Penrose formula used in the canonical full-row-rank statement,
with Mathlib's genuine totalized matrix inverse. Invertibility and the exact
inverse value for the witness must be established; no proposed inverse is
substituted into this definition. -/
def moorePenrose {m n : ℕ} (A : Mat m n) : Mat n m :=
  A.conjTranspose * (A * A.conjTranspose)⁻¹

def IsRightInverse {m n : ℕ} (A : Mat m n) (X : Mat n m) : Prop := A * X = 1

/-- Global minimality among all complex right inverses, not just the displayed
pair or a restricted parameterization. -/
def IsNormMinimizer {m n : ℕ} (A : Mat m n) (p : ℝ) (X : Mat n m) : Prop :=
  IsRightInverse A X ∧
    ∀ Y : Mat n m, IsRightInverse A Y → inducedNorm p X ≤ inducedNorm p Y

def rightInverseNorms {m n : ℕ} (A : Mat m n) (p : ℝ) : Set ℝ :=
  {c | ∃ Y : Mat n m, IsRightInverse A Y ∧ c = inducedNorm p Y}

/-- The complete canonical universal uniqueness conjecture: all dimensions
1 ≤ m < n, all complex full-row-rank A, every finite real p > 2, and every
distinct complex right inverse X. This is the direct-inverse norm, not the
different product objective involving X*A. -/
def RightInverseUniqueConjecture : Prop :=
  ∀ m n : ℕ, 1 ≤ m → m < n → ∀ A : Mat m n, FullRowRank A →
    ∀ p : ℝ, 2 < p → ∀ X : Mat n m,
      IsRightInverse A X → X ≠ moorePenrose A →
        inducedNorm p (moorePenrose A) < inducedNorm p X

/-- The same A printed in Colbrook's theorem and Dokmanić-Gribonval's
Example 4.1, regarded as a complex matrix without any reality restriction
on the vectors or competing right inverses. -/
def witnessA : Mat 2 3 := !![1, 1, 0; 1, 0, 1]

def witnessGram : Mat 2 2 := !![2, 1; 1, 2]

/-- A proposed exact value of the actual inverse of witnessGram. -/
def witnessGramInv : Mat 2 2 := (1 / 3 : ℂ) • !![2, -1; -1, 2]

/-- The source's proposed Moore-Penrose inverse. -/
def witnessB : Mat 3 2 := (1 / 3 : ℂ) • !![1, 1; 2, -1; -1, 2]

def witnessX : Mat 3 2 := !![0, 0; 1, 0; 0, 1]

def normingVector : Vec 2 := ![1, -1]

/-- Exact positive fourth root of two. The link with the manuscript's
2^(1/2-1/p) at p=4 is an explicit theorem obligation. -/
def witnessNorm : ℝ := Real.sqrt (Real.sqrt 2)

end NLA.IE23
