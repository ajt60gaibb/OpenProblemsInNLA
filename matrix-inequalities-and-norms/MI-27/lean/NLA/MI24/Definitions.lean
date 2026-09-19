/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

DRAFT statement boundary, 18 September 2026; not yet typechecked or referee-approved.
Adapted from the preserved 15 September full-target draft; preparation by Codex agent
/root/nm04_final_referee1. No proof bodies have been implemented.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original problem: Ghabries–Abbas–Mourad–Assi; complete convexity deduction:
George Stepaniants. The Heron comparison is credited to Dinh–Dumitru–Franco.
Definitions follow the actual CFC and singular-value APIs used by the accepted
MI21 and MI22 projects. No proof implementation is imported.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Genuine spectral real powers; multiplication below is matrix multiplication. -/
def spectralPower {n : ℕ} (A : Mat n) (r : ℝ) : Mat n := CFC.rpow A r

/-- The actual positive modulus `(X*X)^(1/2)`, never entrywise absolute value. -/
def matrixModulus {n : ℕ} (X : Mat n) : Mat n := CFC.abs X

/-- The exact ordered formula for the geometric mean in the original question. -/
def geometricMean {n : ℕ} (A B : Mat n) : Mat n :=
  spectralPower A (1 / 2) *
    spectralPower (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)) (1 / 2) *
      spectralPower A (1 / 2)

/-- Lin's quantity, with B square roots INSIDE and A square roots OUTSIDE.
For positive definite A its spectral power at -1 is the genuine inverse.
No symmetry under exchanging A and B is stipulated. -/
def linQuantity {n : ℕ} (A B : Mat n) : Mat n :=
  spectralPower A (1 / 2) *
    spectralPower (spectralPower B (1 / 2) * spectralPower A (-1) *
      spectralPower B (1 / 2)) (1 / 2) * spectralPower A (1 / 2)

/-- The exact finite-p Schatten formula in the canonical source. The trace of
this positive matrix is real; taking its real part supplies a real-valued norm.
All advertised finite-p statements require p >= 1. -/
def finiteSchattenNorm {n : ℕ} (p : ℝ) (X : Mat n) : ℝ :=
  Real.rpow (spectralPower (matrixModulus X) p).trace.re (1 / p)

/-- The actual induced norm on complex Euclidean space. No default matrix or
function-space norm is used in place of the p=infinity Schatten norm. -/
def infinitySchattenNorm {n : ℕ} (X : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X‖

/-- Actual singular values, sorted with multiplicity by Mathlib, indexed from 0. -/
def singularValue {n : ℕ} (X : Mat n) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues j

def heronCross {n : ℕ} (A B : Mat n) : Mat n :=
  spectralPower A (1 / 2) * spectralPower B (1 / 2) +
    spectralPower B (1 / 2) * spectralPower A (1 / 2)

def heronEndpoint {n : ℕ} (A B : Mat n) : Mat n :=
  A + B + (2 : ℂ) • geometricMean A B

def middleMatrix {n : ℕ} (A B : Mat n) : Mat n :=
  A + B + geometricMean A B + linQuantity A B

def rightMatrix {n : ℕ} (A B : Mat n) : Mat n :=
  A + B + (2 : ℂ) • linQuantity A B

/-- The COMPLETE unchanged MI-24 statement, splitting [1,infinity] into every
finite real p >= 1 and the infinity endpoint. No Heron inequality, norm axiom,
commutation, matrix comparison or conclusion is an extra premise. -/
def SchattenComplementConjecture : Prop :=
  (∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ p : ℝ, 1 ≤ p →
      finiteSchattenNorm p (middleMatrix A B) ≤
        finiteSchattenNorm p (rightMatrix A B)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    infinitySchattenNorm (middleMatrix A B) ≤
      infinitySchattenNorm (rightMatrix A B))

/-- Real part of the complex trace; products need not themselves be Hermitian. -/
def traceReal {n : ℕ} (X : Mat n) : ℝ := X.trace.re

/-- The two equal-weight, half-power means needed for the published Heron input. -/
def powerHalfP {n : ℕ} (A B : Mat n) : Mat n :=
  (1 / 4 : ℂ) • heronEndpoint A B

def powerHalfQ {n : ℕ} (A B : Mat n) : Mat n :=
  (1 / 4 : ℂ) • (A + B + heronCross A B)

/-- Scalar weight in the actual trace Young argument; its range is proved. -/
def youngWeight (p : ℝ) : ℝ := 1 / (2 * p)

end NLA.MI24
