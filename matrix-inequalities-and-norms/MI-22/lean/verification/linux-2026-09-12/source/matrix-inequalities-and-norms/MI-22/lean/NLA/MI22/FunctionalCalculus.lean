/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Actual CFC bridges for the rational adaptation of Matthew J. Colbrook's MI-22
counterexample. The positivity, congruence and natural-power organization adapts
the campaign's MI-23 and MI-29 proofs; no neighboring project theorem is imported.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization.
-/
import NLA.MI22.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI22

theorem spectralPower_posDef {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    (spectralPower A r).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.rpow A r hA.isStrictlyPositive)

theorem sandwich_posDef {n : ℕ} (X R : Mat n) (hX : X.PosDef) (hR : R.PosDef) :
    (R * X * R).PosDef := by
  simpa only [hR.isHermitian.eq] using
    hX.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hR.isUnit)

theorem spectralPower_add {n : ℕ} (A : Mat n) (hA : A.PosDef) (r s : ℝ) :
    spectralPower A (r + s) = spectralPower A r * spectralPower A s := by
  exact CFC.rpow_add hA.isUnit

theorem spectralPower_nat {n : ℕ} (A : Mat n) (hA : A.PosDef) (k : ℕ) :
    spectralPower A (k : ℝ) = A ^ k := by
  exact CFC.rpow_natCast A k hA.isStrictlyPositive.nonneg

theorem spectralPower_one {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A 1 = A := by
  exact CFC.rpow_one A hA.isStrictlyPositive.nonneg

theorem naturalPower_posDef {n : ℕ} (A : Mat n) (hA : A.PosDef) (k : ℕ) :
    (A ^ k).PosDef := by
  rw [← spectralPower_nat A hA k]
  exact spectralPower_posDef A hA k

theorem spectralPower_naturalPower {n : ℕ} (A : Mat n) (hA : A.PosDef)
    (k : ℕ) (hk : k ≠ 0) (r : ℝ) :
    spectralPower (A ^ k) r = spectralPower A ((k : ℝ) * r) := by
  rw [← spectralPower_nat A hA k]
  exact CFC.rpow_rpow A (k : ℝ) r (by exact_mod_cast hk) hA.isStrictlyPositive

/-- The finite Hermitian functional calculus is the same actual CFC that defines
the real power, for every real exponent on a positive definite matrix. -/
theorem spectral_power_semantics_proved {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    spectralPower A r =
      (hA.isHermitian.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => (((hA.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ)) *
        (hA.isHermitian.eigenvectorUnitary : Mat n).conjTranspose := by
  have hc : CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real (a := A) (y := r) hA.isStrictlyPositive.nonneg
  rw [spectralPower, hc, hA.isHermitian.cfc_eq]
  rfl

end NLA.MI22
