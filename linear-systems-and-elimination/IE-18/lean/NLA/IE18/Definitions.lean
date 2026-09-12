/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to IE-18.
This file contains only the proof-independent mathematical statement boundary.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
open scoped BigOperators NNReal Classical
noncomputable section

namespace NLA.IE18

/-- The sum of coordinate squares, rather than the default norm on a Pi type. -/
def squaredNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i : Fin n, v i ^ 2

/-- The actual Euclidean norm of a real coordinate vector. -/
def euclideanNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (squaredNorm v)

/-- The scalar coefficient in the canonical residual map, using `A=I-M`.
At zero it is totalized by real division; `residualMap` handles zero explicitly. -/
def residualCoefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : ℝ :=
  dotProduct v ((1 - M).mulVec v) / squaredNorm ((1 - M).mulVec v)

/-- Two original Anderson steps. The canonical map explicitly sends zero to zero. -/
def residualMap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  if v = 0 then 0
  else M.mulVec (v - residualCoefficient M v • (1 - M).mulVec v)

/-- Four original Anderson steps, namely two applications of the residual map. -/
def fourStepResidual {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ := residualMap M (residualMap M v)

/-- The unsquared Euclidean norm amplification appearing in IE-18. -/
def amplification {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : ℝ :=
  euclideanNorm (fourStepResidual M v) / euclideanNorm v

/-- Actual amplifications at every nonzero vector, with no default maximum. -/
def amplificationSet {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {r | ∃ v : Fin n → ℝ, v ≠ 0 ∧ r = amplification M v}

/-- The pairwise quotient. Real division gives zero if the denominator is zero,
which implements the canonical zero-denominator convention. -/
def pairQuotient (a b : ℝ) : ℝ :=
  a * b * (b - a) / (|a * (a - 1)| + |b * (b - 1)|)

/-- The square already present in the proposed *norm* amplification factor. -/
def pairValue (a b : ℝ) : ℝ := pairQuotient a b ^ 2

/-- The maximum over distinct eigenvalue indices, retaining multiplicity.
The NNReal square equals the real square in `pairValue`; its finite supremum
is a true maximum for `n≥2`. The empty-index convention is outside that domain. -/
def pairListMaximum {n : ℕ} (μ : Fin n → ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2)).sup
    (fun ij => ‖pairQuotient (μ ij.1) (μ ij.2)‖₊ ^ 2) : ℝ≥0)

/-- The proposed factor using Mathlib's actual full eigenvalue list.
No user-supplied spectral certificate or diagonalization is assumed. -/
def pairMaximum {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) : ℝ := pairListMaximum hM.eigenvalues

/-- The complete original maximum identity. Over `ℝ`, `IsHermitian` is symmetry.
`IsGreatest` says the proposed value is attained and bounds every actual
amplification, without a totalized real supremum on an arbitrary set. -/
def FourStepConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ M : Matrix (Fin n) (Fin n) ℝ, M ≠ 0 →
    ∀ hM : M.IsHermitian, (1 : ℝ) ∉ spectrum ℝ M →
      IsGreatest (amplificationSet M) (pairMaximum hM)

/-- The three exact diagonal entries of Colbrook's positive definite witness. -/
def witnessEigenvalues : Fin 3 → ℝ := ![1 / 10, 1 / 2, 3 / 5]

def witnessMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal witnessEigenvalues

def witnessInitial : Fin 3 → ℝ := ![1, 1, 1]

/-- The proposed first residual, to be derived from the actual map. -/
def witnessFirst : Fin 3 → ℝ := ![-2 / 61, 8 / 61, 15 / 61]

/-- The proposed four-step residual, to be derived from the actual composition. -/
def witnessSecond : Fin 3 → ℝ := ![289 / 84241, -756 / 84241, 1125 / 84241]

end NLA.IE18
