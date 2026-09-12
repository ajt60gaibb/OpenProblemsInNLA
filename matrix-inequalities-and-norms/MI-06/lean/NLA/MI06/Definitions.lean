/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Statement definitions for Matthew J. Colbrook's counterexample to MI-06.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder Matrix MatrixOrder
noncomputable section

namespace NLA.MI06

/-- The genuine positive modulus, defined by continuous functional calculus. -/
def matrixModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.abs X

/-- The arithmetic average of the right and left moduli. -/
def symmetricModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (matrixModulus X + matrixModulus X.conjTranspose)

/-- Conjugation by an arbitrary genuine complex unitary matrix. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) * H *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- The complete canonical assertion, with ordinary positive-semidefinite order. -/
def DominationConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
      symmetricModulus (A + B) ≤
        (Real.sqrt 2 : ℂ) •
          (unitaryConjugate U (symmetricModulus A) +
            unitaryConjugate V (symmetricModulus B))

/-- Squared Euclidean length, explicit to avoid a default function sup norm. -/
def squaredLength {n : ℕ} (w : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (w i)

/-- The real part of the actual Hermitian quadratic form. -/
def quadraticForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → ℂ) : ℝ :=
  (star w ⬝ᵥ (H *ᵥ w)).re

/-- The actual rank-one matrix `w w*`. -/
def rankOne {n : ℕ} (w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec w (star w)

/-- Colbrook's family specialized to the fixed rational parameter `t = 3/4`. -/
def witnessA : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 3 / 4, 0; 0, 0, 0; 0, 0, 0]

def witnessB : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1, 0, 0; 0, 0, 0; -3 / 4, 0, 0]

/-- Proposed exact values; their identification with CFC moduli is a proof obligation. -/
def rightModulusA : Matrix (Fin 3) (Fin 3) ℂ :=
  !![4 / 5, 3 / 5, 0; 3 / 5, 9 / 20, 0; 0, 0, 0]

def axialModulus : Matrix (Fin 3) (Fin 3) ℂ :=
  !![5 / 4, 0, 0; 0, 0, 0; 0, 0, 0]

def leftModulusB : Matrix (Fin 3) (Fin 3) ℂ :=
  !![4 / 5, 0, 3 / 5; 0, 0, 0; 3 / 5, 0, 9 / 20]

def rightModulusSum : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3 / 4, 0, 0; 0, 3 / 4, 0; 0, 0, 0]

def leftModulusSum : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3 / 4, 0, 0; 0, 0, 0; 0, 0, 3 / 4]

def symmetricA : Matrix (Fin 3) (Fin 3) ℂ :=
  !![41 / 40, 3 / 10, 0; 3 / 10, 9 / 40, 0; 0, 0, 0]

def symmetricB : Matrix (Fin 3) (Fin 3) ℂ :=
  !![41 / 40, 0, 3 / 10; 0, 0, 0; 3 / 10, 0, 9 / 40]

def symmetricSum : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3 / 4, 0, 0; 0, 3 / 8, 0; 0, 0, 3 / 8]

/-- Unnormalized top directions; no computed eigenvalue is used in the target. -/
def directionA : Fin 3 → ℂ := ![3, 1, 0]

def directionB : Fin 3 → ℂ := ![3, 0, 1]

def missingA : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 0; 0, 0, 1]

def missingB : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 1, 0; 0, 0, 0]

end NLA.MI06
