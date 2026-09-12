/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-21.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
This is the proof-independent mathematical statement boundary.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section

namespace NLA.MI21

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Real powers from the actual continuous functional calculus. On the positive
definite inputs of the conjecture this is spectral matrix exponentiation. -/
def spectralPower {n : ℕ} (A : Mat n) (r : ℝ) : Mat n := CFC.rpow A r

/-- The weighted geometric mean in the exact order written in the canonical target.
The exponents `1/2`, `-1/2` and `t` are real spectral powers. -/
def geometricMean {n : ℕ} (A B : Mat n) (t : ℝ) : Mat n :=
  spectralPower A (1 / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) t *
      spectralPower A (1 / 2)

/-- A complex norm on the full matrix vector space, with independent left and
right unitary invariance. These are the usual norm axioms, not an operator-norm
restriction. Both unitary inverse identities are stated explicitly. -/
def IsUnitaryInvariantNorm {n : ℕ} (ν : Mat n → ℝ) : Prop :=
  (∀ X, 0 ≤ ν X) ∧
  (∀ X, ν X = 0 ↔ X = 0) ∧
  (∀ X Y, ν (X + Y) ≤ ν X + ν Y) ∧
  (∀ (z : ℂ) X, ν (z • X) = ‖z‖ * ν X) ∧
  (∀ U V X : Mat n, Uᴴ * U = 1 → U * Uᴴ = 1 →
    Vᴴ * V = 1 → V * Vᴴ = 1 → ν (U * X * V) = ν X)

/-- The genuine operator norm of the matrix acting on complex Euclidean space.
This explicit construction avoids the default entrywise matrix norm. -/
def operatorNorm {n : ℕ} (A : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖

/-- The sum of the powered weighted means on the left of MI-21. -/
def leftMatrix {m n : ℕ} (A B : Fin m → Mat n) (s t r : ℝ) : Mat n :=
  ∑ i, spectralPower (geometricMean (spectralPower (A i) s)
    (spectralPower (B i) s) t) r

/-- The right side uses the actual aggregate sums and the original order of
the three noncommuting factors before its final real power. -/
def rightMatrix {m n : ℕ} (A B : Fin m → Mat n) (s t r p : ℝ) : Mat n :=
  spectralPower
    (spectralPower (∑ i, A i) ((1 - t) * s * r * p / 2) *
      spectralPower (∑ i, B i) (t * s * r * p) *
        spectralPower (∑ i, A i) ((1 - t) * s * r * p / 2)) (1 / p)

/-- The complete original MI-21 assertion: all positive dimensions and numbers
of summands, all positive definite complex inputs, all allowed real parameters,
and every unitarily invariant norm. -/
def GeometricMeanNormConjecture : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ A B : Fin m → Mat n,
    (∀ i, (A i).PosDef) → (∀ i, (B i).PosDef) →
    ∀ t s r p : ℝ, 0 ≤ t → t ≤ 1 → 0 < s → 0 < r → 0 < p → 1 ≤ s * r →
    ∀ ν : Mat n → ℝ, IsUnitaryInvariantNorm ν →
      ν (leftMatrix A B s t r) ≤ ν (rightMatrix A B s t r p)

/-- The first positive diagonal matrix in Colbrook's witness. -/
def witnessC : Mat 2 := Matrix.diagonal (![12 / 37, 21 / 29] : Fin 2 → ℂ)

/-- The second positive diagonal matrix in Colbrook's witness. -/
def witnessE : Mat 2 := Matrix.diagonal (![35 / 37, 20 / 29] : Fin 2 → ℂ)

/-- The source's real symmetric involution, regarded as a complex matrix.
Its unitarity is a proof obligation, not an assumption. -/
def witnessS : Mat 2 := (1 / 17 : ℂ) • !![15, 8; 8, -15]

def witnessA : Fin 2 → Mat 2 := ![witnessC ^ (2 : ℕ), witnessE ^ (2 : ℕ)]

def witnessB : Fin 2 → Mat 2 :=
  ![witnessS * witnessE ^ (2 : ℕ) * witnessS,
    witnessS * witnessC ^ (2 : ℕ) * witnessS]

/-- A candidate rational expression for the actual left matrix.
The equality to `leftMatrix` is required by the counterexample theorem. -/
def witnessL : Mat 2 :=
  (1 / 12158163 : ℂ) • !![8216600, -985600; -985600, 11912600]

def witnessVector : Fin 2 → ℂ := ![1, -4]

def witnessEigenvalue : ℝ := 1351000 / 1350907

end NLA.MI21
