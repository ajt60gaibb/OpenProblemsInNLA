/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-29.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
This file is the proof-independent mathematical statement boundary.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI29

/-- The actual unital continuous-functional-calculus power.
The explicit `CFC.rpow` avoids any pointwise function-power instance on matrices.
For a positive semidefinite matrix, exponent zero gives the identity matrix. -/
def spectralPower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.rpow A r

/-- The actual matrix modulus, `CFC.sqrt (Xᴴ * X)`.
Mathlib's `CFC.abs` uses the positive square root from functional calculus. -/
def matrixModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.abs X

def leftMatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  spectralPower A k + spectralPower (matrixModulus (A * B)) p

def rightMatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  spectralPower A k + spectralPower (matrixModulus (B * A)) p

def leftDet {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) : ℂ :=
  (leftMatrix A B k p).det

def rightDet {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k p : ℝ) : ℂ :=
  (rightMatrix A B k p).det

/-- The complete canonical MI-29 target, with arbitrary nonnegative real powers.
`IsUnit B` means invertibility in the square matrix ring.
The complex order compares real parts with equal imaginary parts; the required
generic reality/positivity theorem separately verifies that both determinants
are positive real numbers under these hypotheses. -/
def ModulusDeterminantConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef → B.IsHermitian → IsUnit B →
      ∀ k p : ℝ, 0 ≤ k → 0 ≤ p → rightDet A B k p ≤ leftDet A B k p

/-- Colbrook's positive definite diagonal base, regarded as a complex matrix. -/
def witnessA : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (![2, 1, 1 / 2] : Fin 3 → ℂ)

/-- The integer matrix `M = 5 B` in the source's exact calculation. -/
def witnessM : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 2, 0; 2, 1, 2; 0, 2, 1]

/-- The admissible indefinite Hermitian factor. Invertibility is not assumed. -/
def witnessB : Matrix (Fin 3) (Fin 3) ℂ := (1 / 5 : ℂ) • witnessM

end NLA.MI29
