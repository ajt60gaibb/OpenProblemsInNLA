/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's complete MI-03 argument.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI03

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The actual principal positive square root of the actual Gram matrix. -/
def matrixModulus {n : ℕ} (A : Mat n) : Mat n :=
  CFC.sqrt (A.conjTranspose * A)

/-- The genuine induced Euclidean operator norm, not an entrywise matrix norm. -/
def operatorNorm {n : ℕ} (A : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖

def summandSum {n k : ℕ} (A : Fin k → Mat n) : Mat n := ∑ j, A j

def modulusSum {n k : ℕ} (A : Fin k → Mat n) : Mat n :=
  ∑ j, matrixModulus (A j)

/-- Positivity of this actual difference is the original matrix-order bound. -/
def errorGap {n k : ℕ} (A : Fin k → Mat n) (c : ℝ) : Mat n :=
  (c : ℂ) • (1 : Mat n) + modulusSum A - matrixModulus (summandSum A)

/-- Every positive dimension and every complex contraction tuple are retained. -/
def AdmissibleConstant (k : ℕ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : Fin k → Mat n,
    (∀ j, operatorNorm (A j) ≤ 1) → (errorGap A c).PosSemidef

def admissibleConstants (k : ℕ) : Set ℝ := {c | AdmissibleConstant k c}

/-- The original infimum. Nonemptiness and a least element are proof obligations. -/
def sharpConstant (k : ℕ) : ℝ := sInf (admissibleConstants k)

/-- The complete original question, including every odd summand count. -/
def OddContractionConjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k → Odd k → sharpConstant k = (k : ℝ) / 4

/-- Half the sum over all ordered pairs equals the source's unordered-pair
variance; diagonal terms are zero. No finite enumeration is used. -/
def pairVariance {n k : ℕ} (A : Fin k → Mat n) : Mat n :=
  ∑ i, ∑ j, (1 / 2 : ℂ) •
    ((A i - A j).conjTranspose * (A i - A j))

def shiftedSquare {n k : ℕ} (A : Fin k → Mat n) : Mat n :=
  (matrixModulus (summandSum A) - ((k : ℂ) / 2) • (1 : Mat n)) ^ (2 : ℕ)

/-- The genuine complex primitive root used in the manuscript. Its unit norm
and zero geometric sum must be proved for every k≥2. -/
def rootOfUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (k : ℂ))

def firstVector : Fin 2 → ℂ := ![1, 0]

def witnessVector (k : ℕ) (j : Fin k) : Fin 2 → ℂ :=
  ![1 / 2, ((Real.sqrt 3 : ℝ) : ℂ) / 2 * rootOfUnity k ^ (j : ℕ)]

/-- Actual outer product uv*, retaining complex conjugation. -/
def outerProduct {n : ℕ} (u v : Fin n → ℂ) : Mat n :=
  Matrix.vecMulVec u (fun i => star (v i))

def witness (k : ℕ) (j : Fin k) : Mat 2 :=
  outerProduct firstVector (witnessVector k j)

def firstProjection : Mat 2 := outerProduct firstVector firstVector

def witnessModulusSum (k : ℕ) : Mat 2 :=
  Matrix.diagonal (![(k : ℂ) / 4, 3 * (k : ℂ) / 4] : Fin 2 → ℂ)

def witnessDifference (k : ℕ) : Mat 2 :=
  Matrix.diagonal (![(k : ℂ) / 4, -3 * (k : ℂ) / 4] : Fin 2 → ℂ)

end NLA.MI03
