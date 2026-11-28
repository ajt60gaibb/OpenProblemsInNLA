/-
  MI20/Definitions.lean
  =====================
  Author: Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Core definitions: matrix modulus `matAbs`, singular values, Schatten-p norms, and Lee constants.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Polar modulus |A| = (Aᴴ * A)^(1/2) via continuous functional calculus square root. -/
def matAbs {n : ℕ} (A : Mat n) : Mat n := CFC.sqrt (Aᴴ * A)

/-- Singular values of A (descending, via Mathlib's Euclidean linear map). -/
def singularValue {n : ℕ} (A : Mat n) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- Schatten p-power: ∑_{i : Fin n} σ_i(A)^p. -/
def schattenPow (p : ℝ) {n : ℕ} (A : Mat n) : ℝ :=
  ∑ i : Fin n, (singularValue A i) ^ p

/-- Schatten p-norm: (∑_i σ_i(A)^p)^(1/p). -/
def schattenNorm (p : ℝ) {n : ℕ} (A : Mat n) : ℝ :=
  (schattenPow p A) ^ (1 / p)

/-- Lee ratio for an m-tuple of n × n complex matrices. -/
def leeRatio (p : ℝ) {m n : ℕ} (A : Fin m → Mat n) : ℝ :=
  schattenNorm p (∑ k, A k) / schattenNorm p (∑ k, matAbs (A k))

/-- n-dimensional complex Lee constant C_{p,m}(n). -/
def leeConst (p : ℝ) (m n : ℕ) : ℝ :=
  sSup { r : ℝ | ∃ A : Fin m → Mat n, (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A }

/-- All-dimensional complex Lee constant C_{p,m}(∞) = sup_{n ≥ 1} C_{p,m}(n). -/
def leeConstInf (p : ℝ) (m : ℕ) : ℝ :=
  sSup { r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = leeConst p m n }

end MI20
