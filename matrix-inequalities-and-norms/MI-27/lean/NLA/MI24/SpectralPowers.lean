/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Concrete matrix bridges to Mathlib's continuous functional calculus. Matrix
positive definiteness is equivalent to IsStrictlyPositive; negative powers
are matched to the actual nonsingular matrix inverse, not an assumed symbol.
-/
import NLA.MI24.Definitions

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma spectralPower_nonneg {n : ℕ} (A : Mat n) (r : ℝ) :
    0 ≤ spectralPower A r := by
  exact CFC.rpow_nonneg

lemma spectralPower_posDef {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    (spectralPower A r).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.rpow A r hA.isStrictlyPositive)

lemma spectralPower_isHermitian {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    (spectralPower A r).IsHermitian :=
  (spectralPower_posDef A hA r).isHermitian

lemma spectralPower_isUnit {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    IsUnit (spectralPower A r) :=
  (spectralPower_posDef A hA r).isUnit

lemma spectralPower_zero {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A 0 = 1 := by
  exact CFC.rpow_zero A hA.posSemidef.nonneg

lemma spectralPower_one {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A 1 = A := by
  exact CFC.rpow_one A hA.posSemidef.nonneg

lemma spectralPower_mul {n : ℕ} (A : Mat n) (hA : A.PosDef) (r s : ℝ) :
    spectralPower A r * spectralPower A s = spectralPower A (r + s) := by
  exact (CFC.rpow_add (a := A) (x := r) (y := s) hA.isUnit).symm

lemma spectralPower_mul_neg {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    spectralPower A r * spectralPower A (-r) = 1 := by
  exact CFC.rpow_mul_rpow_neg r hA.isStrictlyPositive

lemma spectralPower_neg_mul {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    spectralPower A (-r) * spectralPower A r = 1 := by
  exact CFC.rpow_neg_mul_rpow r hA.isStrictlyPositive

/-- Ring.inverse agrees with Mathlib's nonsingular matrix inverse. This bridge
retains the actual inverse used by the original problem and frozen definitions. -/
theorem spectral_power_inverse {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.PosDef) : spectralPower A (-1) = A⁻¹ := by
  simpa only [spectralPower, CFC.rpow_eq_pow, Matrix.nonsing_inv_eq_ringInverse]
    using (CFC.inverse_eq_rpow_neg_one hA.isStrictlyPositive).symm

lemma spectralPower_half_eq_sqrt {n : ℕ} (A : Mat n) :
    spectralPower A (1 / 2) = CFC.sqrt A := by
  exact (CFC.sqrt_eq_rpow (a := A)).symm

lemma spectralPower_half_mul_self {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A (1 / 2) * spectralPower A (1 / 2) = A := by
  rw [spectralPower_half_eq_sqrt]
  exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

lemma spectralPower_half_unique {n : ℕ} (A B : Mat n)
    (hB : B.PosDef) (hBB : B * B = A) : spectralPower A (1 / 2) = B := by
  rw [spectralPower_half_eq_sqrt]
  exact CFC.sqrt_unique hBB hB.posSemidef.nonneg

lemma posDef_hermitian_sandwich {n : ℕ} (A S : Mat n)
    (hA : A.PosDef) (hS : S.IsHermitian) (hu : IsUnit S) :
    (S * A * S).PosDef := by
  simpa only [hS.star_eq] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := A) hu).mpr hA

end NLA.MI24
