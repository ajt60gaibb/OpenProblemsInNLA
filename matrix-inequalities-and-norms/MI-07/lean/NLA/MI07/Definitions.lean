/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Statement definitions for Matthew J. Colbrook's counterexample to MI-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Topology
noncomputable section

namespace NLA.MI07

/-- The actual positive modulus from continuous functional calculus. -/
def matrixModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := CFC.abs X

/-- The canonical sequence uses every positive integer exponent, indexed by `r+1`.
The outer exponent is a real CFC power, and the inner powers are matrix ring powers. -/
def rootSequence {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.rpow (matrixModulus X ^ (r + 1) +
    matrixModulus X.conjTranspose ^ (r + 1)) (((r + 1 : ℕ) : ℝ)⁻¹)

/-- Actual finite-dimensional limit of the canonical CFC sequence.
`limUnder` is totalized away from convergence. Every counterexample occurrence
has its convergence proved explicitly; its default value is never used. -/
def maximalModulus {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Filter.limUnder Filter.atTop (rootSequence X)

open scoped Matrix.Norms.L2Operator in
/-- The genuine Euclidean operator norm, explicitly scoped to avoid a default entrywise norm. -/
def spectralNorm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖X‖

/-- Conjugation by an arbitrary genuine unitary matrix. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) * H *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- The original constant-one triangle conjecture, in ordinary PSD order. -/
def TriangleConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
      maximalModulus (A + B) ≤
        unitaryConjugate U (maximalModulus A) + unitaryConjugate V (maximalModulus B)

/-- Colbrook's rank-one family, specialized to the rational parameter `t=5/12`. -/
def witnessA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

def witnessB : Matrix (Fin 2) (Fin 2) ℂ := !![0, 5 / 12; 0, 0]

/-- The projection onto the unit vector `(12/13,5/13)`. -/
def directionProjector : Matrix (Fin 2) (Fin 2) ℂ :=
  !![144 / 169, 60 / 169; 60 / 169, 25 / 169]

/-- Sum of the two distinct rank-one polar-direction projections. -/
def spanningSum : Matrix (Fin 2) (Fin 2) ℂ := witnessA + directionProjector

end NLA.MI07
