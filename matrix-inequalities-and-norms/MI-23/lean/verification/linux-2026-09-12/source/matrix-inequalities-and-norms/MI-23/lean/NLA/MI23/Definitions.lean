/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-23.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
This is the proof-independent mathematical statement boundary.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI23

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The genuine continuous-functional-calculus real power. This is not
entrywise exponentiation or a rational proxy for spectral exponentiation. -/
def spectralPower {n : ℕ} (A : Mat n) (r : ℝ) : Mat n := CFC.rpow A r

/-- The generalized geometric mean, retaining the exact noncommuting factor order
and the independent real parameters `r` and `t` from the canonical target. -/
def generalizedMean {n : ℕ} (A B : Mat n) (r t : ℝ) : Mat n :=
  spectralPower A (r / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t *
      spectralPower A (r / 2)

/-- Actual characteristic-polynomial roots with algebraic multiplicity, mapped
to their real parts and sorted decreasingly. On products of positive definite
matrices the required semantic theorem proves every root is real and positive,
the list has exactly `n` entries, and no root or multiplicity is discarded.
No fallback Hermitian matrix or assumed numerical eigenvalue list is used. -/
def orderedEigenvalues {n : ℕ} (A : Mat n) : List ℝ :=
  (A.charpoly.roots.map Complex.re).sort (· ≥ ·)

/-- Complete semantic obligations for the ordered list, including every complex
root with multiplicity and the genuine determinant. -/
def HasOrderedPositiveEigenvalues {n : ℕ} (A : Mat n) : Prop :=
  (orderedEigenvalues A).length = n ∧
    (orderedEigenvalues A).Pairwise (· ≥ ·) ∧
    (∀ a ∈ orderedEigenvalues A, 0 < a) ∧
    A.charpoly.roots =
      (↑((orderedEigenvalues A).map (fun a : ℝ => (a : ℂ))) : Multiset ℂ) ∧
    (((orderedEigenvalues A).prod : ℝ) : ℂ) = A.det

/-- Log-majorization for equal-length lists: all proper nonempty prefix products
are bounded and the complete products are equal. Positivity and decreasing order
of every list arising in the conjecture are separate proved semantic obligations.
In particular, this is not weak log-majorization or only its first inequality. -/
def LogMajorized (a b : List ℝ) : Prop :=
  a.length = b.length ∧
    (∀ k : ℕ, 1 ≤ k → k < a.length → (a.take k).prod ≤ (b.take k).prod) ∧
    a.prod = b.prod

/-- The first entry of the actual ordered list. The zero default is irrelevant
on positive-dimensional positive-definite products, whose list length is proved. -/
def largestEigenvalue {n : ℕ} (A : Mat n) : ℝ :=
  (orderedEigenvalues A).getD 0 0

def leftProduct {n : ℕ} (A B : Mat n) (r s p t : ℝ) : Mat n :=
  spectralPower (generalizedMean A B r t) p *
    spectralPower (generalizedMean A B s (1 - t)) p

def rightProduct {n : ℕ} (A B : Mat n) (r s p : ℝ) : Mat n :=
  spectralPower A (p * (r + s - 1)) * spectralPower B p

/-- The complete canonical MI-23 conjecture: all positive dimensions, all complex
positive definite inputs, all real `p ≥ 1`, all `t ∈ [0,1]`, and both original
parameter regions `(r,s ≥ 1)` or `(r,s ≤ 0)`. The conclusion retains the entire
ordered-eigenvalue log-majorization, including equality of the full products. -/
def GeneralizedGeometricMeanConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ r s p t : ℝ, 1 ≤ p → 0 ≤ t → t ≤ 1 →
      ((1 ≤ r ∧ 1 ≤ s) ∨ (r ≤ 0 ∧ s ≤ 0)) →
        LogMajorized (orderedEigenvalues (leftProduct A B r s p t))
          (orderedEigenvalues (rightProduct A B r s p))

/-- The genuine operator norm on complex Euclidean space, made explicit to avoid
the default entrywise norm on matrix function types. -/
def operatorNorm {n : ℕ} (A : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖

/-- Squared Frobenius norm, with the complex squared modulus of every entry. -/
def frobeniusSquared {n : ℕ} (A : Mat n) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- Colbrook's exact diagonal factor. -/
def witnessD : Mat 3 := Matrix.diagonal (![16, 1 / 12, 1] : Fin 3 → ℂ)

def witnessDInv : Mat 3 := Matrix.diagonal (![1 / 16, 12, 1] : Fin 3 → ℂ)

/-- The source's integer positive definite matrix. Positivity is proved later. -/
def witnessT : Mat 3 := !![2, 1, 2; 1, 25, -10; 2, -10, 10]

/-- A rational unit lower-triangular factor for exact positivity certification. -/
def witnessL : Mat 3 := !![1, 0, 0; 1 / 2, 1, 0; 1, -22 / 49, 1]

def witnessPivots : Mat 3 :=
  Matrix.diagonal (![2, 49 / 2, 150 / 49] : Fin 3 → ℂ)

def witnessA : Mat 3 := witnessD ^ (2 : ℕ)

def witnessB : Mat 3 := witnessD * witnessT ^ (8 : ℕ) * witnessD

/-- Rational candidate values of the actual means; their CFC identities are
explicit proof obligations, never assumptions or replacements in the target. -/
def witnessG : Mat 3 := witnessD * witnessT * witnessD

def witnessH : Mat 3 := witnessD * witnessT ^ (7 : ℕ) * witnessD

/-- The exact positive separation from the manuscript. Only this single rational
point inequality is planned for LeanCert; no eigenvalue approximation is needed. -/
def squaredGap : ℝ := 99434824489435745411095588895 / 107495424

end NLA.MI23
