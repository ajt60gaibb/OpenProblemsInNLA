/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of the full MI-22 target, using a rational witness adapted from
Matthew J. Colbrook's counterexample. The adapted B below is not the matrix
printed in Colbrook's manuscript; see SOURCE_CORRESPONDENCE.md.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI22

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The genuine real power from continuous functional calculus. It is never
replaced by entrywise powers or an assumed rational matrix certificate. -/
def spectralPower {n : ℕ} (A : Mat n) (t : ℝ) : Mat n := CFC.rpow A t

/-- The exact weighted mean, with the original noncommuting order of factors. -/
def weightedMean {n : ℕ} (A B : Mat n) (t : ℝ) : Mat n :=
  spectralPower A (1 / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t *
      spectralPower A (1 / 2)

def leftProduct {n : ℕ} (A B : Mat n) (t : ℝ) : Mat n :=
  spectralPower A t * weightedMean A B t * spectralPower B (1 - t)

/-- Mathlib's actual singular values of the linear map on complex Euclidean
space: descending, repeated with multiplicity, and zero beyond dimension n.
The index zero is the first singular value. No user-supplied list is involved. -/
def singularValue {n : ℕ} (A : Mat n) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- The first k actual singular values, with the original one-based range
1,...,k represented as the zero-based range 0,...,k-1. -/
def singularPrefix {n : ℕ} (A : Mat n) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, singularValue A j

/-- Full log-majorization, including equality at n rather than weak
log-majorization. Both matrices have the same actual dimension n. -/
def SingularLogMajorized {n : ℕ} (X Y : Mat n) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < n → singularPrefix X k ≤ singularPrefix Y k) ∧
    singularPrefix X n = singularPrefix Y n

/-- Every positive dimension, every complex positive definite pair, and every
real t in the closed interval [0,1], exactly as in the retained canonical target. -/
def WeightedLogMajorizationConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → SingularLogMajorized (leftProduct A B t) (A * B)

/-- Actual induced Euclidean operator norm, made explicit to avoid a default
entrywise matrix norm. -/
def operatorNorm {n : ℕ} (A : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖

/-- Actual squared Frobenius norm, summing the squared complex modulus of every entry. -/
def frobeniusSquared {n : ℕ} (A : Mat n) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

def witnessD : Mat 3 := Matrix.diagonal (![16, 1 / 16, 1] : Fin 3 → ℂ)

def witnessDInv : Mat 3 := Matrix.diagonal (![1 / 16, 16, 1] : Fin 3 → ℂ)

/-- This A is the same diagonal matrix as in the source, diag(256,1/256,1). -/
def witnessA : Mat 3 := witnessD ^ (2 : ℕ)

/-- Exact small-denominator adaptation of the source's rational root R,
rounding its entries to the nearest multiple of 1/8192. Rounding is only how
this candidate was selected; no approximate-root assertion is assumed. -/
def witnessT : Mat 3 :=
  (1 / 8192 : ℂ) • !![4616, -39, -1250; -39, 55069, -1519; -1250, -1519, 6499]

/-- Rational unit lower triangular factor for direct exact positivity certification. -/
def witnessLDL : Mat 3 :=
  !![1, 0, 0; -39 / 4616, 1, 0; -625 / 2308, -7060454 / 254196983, 1]

def witnessPivots : Mat 3 :=
  Matrix.diagonal (![577 / 1024, 254196983 / 37814272,
    1555181999141 / 2082381684736] : Fin 3 → ℂ)

/-- The adapted matrix B, defined by an exact eighth power. It is deliberately
distinguished from the source's printed integer B. Positivity is a theorem. -/
def witnessB : Mat 3 := witnessD * witnessT ^ (8 : ℕ) * witnessD

/-- Proposed value of A^(1/8), whose genuine CFC identity must be proved. -/
def witnessAOneEighth : Mat 3 :=
  Matrix.diagonal (![2, 1 / 2, 1] : Fin 3 → ℂ)

/-- Proposed value of A^(5/8), as an exact diagonal matrix. -/
def witnessAFiveEighths : Mat 3 :=
  Matrix.diagonal (![32, 1 / 32, 1] : Fin 3 → ℂ)

/-- The other root remains the actual CFC root of B; it is not approximated. -/
def witnessRoot : Mat 3 := spectralPower witnessB (1 / 8)

/-- A rational matrix that will be proved equal to the actual left product
multiplied on the right by witnessRoot. -/
def witnessN : Mat 3 := witnessAFiveEighths * witnessT * witnessD * witnessB

/-- A genuine Euclidean vector, with norm one to be proved exactly. -/
def witnessVector : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (![0, 4 / 5, -3 / 5] : Fin 3 → ℂ)

/-- Real part of an actual coordinate of a matrix acting on a Euclidean vector. -/
def witnessTestValue : ℝ :=
  ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) witnessN) witnessVector 0).re

end NLA.MI22
