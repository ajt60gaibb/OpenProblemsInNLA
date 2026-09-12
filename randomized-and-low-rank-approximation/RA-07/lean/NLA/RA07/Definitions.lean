/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Statement definitions for Matthew J. Colbrook's affirmative resolution of RA-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Data.Real.Basic

set_option autoImplicit false
open scoped BigOperators Polynomial
noncomputable section

namespace NLA.RA07

/-- The actual canonical sum over all subsets of the indicated cardinality. -/
def elementarySymmetric {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).powersetCard j).sum fun S => S.prod lam

/-- The exact sequence in RA-07, defined using ordinary real division. -/
def errorSequence {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) * elementarySymmetric lam (j + 1) / elementarySymmetric lam j

/-- The actual product generating polynomial, not an assumed coefficient list. -/
def generatingPolynomial {n : ℕ} (lam : Fin n → ℝ) : ℝ[X] :=
  ∏ i : Fin n, (1 + Polynomial.C (lam i) * Polynomial.X)

/-- Apply actual polynomial differentiation exactly `d` times. -/
def iteratedGeneratingDerivative {n : ℕ} (lam : Fin n → ℝ) (d : ℕ) : ℝ[X] :=
  (Polynomial.derivative^[d]) (generatingPolynomial lam)

/-- Power sums of the positive reciprocal roots used in the exact certificate. -/
def powerSum {m : ℕ} (μ : Fin m → ℝ) (r : ℕ) : ℝ :=
  ∑ a, μ a ^ r

/-- Each unordered pair is counted exactly once by the strict order on `Fin m`. -/
def pairGap {m : ℕ} (μ : Fin m → ℝ) : ℝ :=
  ∑ a : Fin m, ∑ b ∈ (Finset.univ : Finset (Fin m)).filter (fun b => a < b),
    μ a * μ b * (μ a - μ b) ^ 2

/-- The denominator whose strict positivity must be established in the proof. -/
def certificateDenominator {m : ℕ} (μ : Fin m → ℝ) : ℝ :=
  powerSum μ 1 * (powerSum μ 1 ^ 2 - powerSum μ 2)

/-- The full canonical assertion, with its original dimension and index ranges. -/
def ConvexityConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ lam : Fin n → ℝ, (∀ i, 0 < lam i) →
    ∀ j : ℕ, 2 ≤ j → j ≤ n - 1 →
      0 ≤ errorSequence lam (j - 1) - 2 * errorSequence lam j + errorSequence lam (j + 1)

end NLA.RA07
