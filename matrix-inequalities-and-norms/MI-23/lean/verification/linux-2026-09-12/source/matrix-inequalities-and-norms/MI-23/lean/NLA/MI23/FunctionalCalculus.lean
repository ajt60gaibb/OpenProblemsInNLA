/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Generic analytic bridges for Matthew J. Colbrook's MI-23 counterexample.
The positive-power and congruence API patterns reuse the campaign's MI-29/MI-21
formalizations; no theorem from another NLA project is imported.
-/
import NLA.MI23.Definitions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI23

theorem spectralPower_posDef {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    (spectralPower A r).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.rpow A r hA.isStrictlyPositive)

theorem sandwich_posDef {n : ℕ} (X R : Mat n) (hX : X.PosDef) (hR : R.PosDef) :
    (R * X * R).PosDef := by
  simpa only [hR.isHermitian.eq] using
    hX.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hR.isUnit)

theorem positive_powers_and_means_proved {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (r t : ℝ) :
    (spectralPower A r).PosDef ∧ (generalizedMean A B r t).PosDef := by
  refine ⟨spectralPower_posDef A hA r, ?_⟩
  have hm := sandwich_posDef B (spectralPower A (-1 / 2)) hB
    (spectralPower_posDef A hA (-1 / 2))
  exact sandwich_posDef _ _ (spectralPower_posDef _ hm t)
    (spectralPower_posDef A hA (r / 2))

theorem ordered_eigenvalues_posDef {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    HasOrderedPositiveEigenvalues A := by
  have hroots := hA.isHermitian.roots_charpoly_eq_eigenvalues
  have hreal : A.charpoly.roots.map Complex.re =
      Finset.univ.val.map hA.isHermitian.eigenvalues := by
    rw [hroots, Multiset.map_map]
    congr 1
  have hsort : (↑(orderedEigenvalues A) : Multiset ℝ) =
      Finset.univ.val.map hA.isHermitian.eigenvalues := by
    simp only [orderedEigenvalues, Multiset.sort_eq, hreal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [orderedEigenvalues, Multiset.length_sort, hreal, Multiset.card_map,
      Finset.card_val, Finset.card_univ, Fintype.card_fin]
  · exact Multiset.pairwise_sort _ _
  · intro a ha
    have hm : a ∈ Finset.univ.val.map hA.isHermitian.eigenvalues := by
      rw [← hsort]
      exact ha
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hm
    exact hA.eigenvalues_pos i
  · rw [← Multiset.map_coe, hsort, Multiset.map_map]
    exact hroots
  · have hp : (orderedEigenvalues A).prod = ∏ i, hA.isHermitian.eigenvalues i := by
      change (↑(orderedEigenvalues A) : Multiset ℝ).prod = _
      rw [hsort]
      rfl
    rw [hp, hA.isHermitian.det_eq_prod_eigenvalues]
    simp only [Complex.ofReal_prod]
    rfl


theorem orderedEigenvalues_congr {n : ℕ} {A B : Mat n}
    (h : A.charpoly = B.charpoly) : orderedEigenvalues A = orderedEigenvalues B := by
  simp only [orderedEigenvalues, h]

theorem positive_eigenvalues_of_charpoly_eq {n : ℕ} {A B : Mat n}
    (h : A.charpoly = B.charpoly) (hB : HasOrderedPositiveEigenvalues B) :
    HasOrderedPositiveEigenvalues A := by
  have hd : A.det = B.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, h]
  simpa only [HasOrderedPositiveEigenvalues, orderedEigenvalues_congr h, h, hd] using hB

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

theorem product_eigenvalue_semantics_proved {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    let R := spectralPower Y (1 / 2)
    let Rinv := spectralPower Y (-1 / 2)
    let S := R * X * R
    S.PosDef ∧ R * Rinv = 1 ∧ Rinv * R = 1 ∧
      R * (X * Y) * Rinv = S ∧ (X * Y).charpoly = S.charpoly ∧
      HasOrderedPositiveEigenvalues (X * Y) := by
  dsimp only
  let R := spectralPower Y (1 / 2)
  let Rinv := spectralPower Y (-1 / 2)
  have hRi : R * Rinv = 1 := by
    rw [show R * Rinv = spectralPower Y ((1 / 2) + (-1 / 2)) from
      (spectralPower_add Y hY _ _).symm]
    norm_num
    exact CFC.rpow_zero Y hY.isStrictlyPositive.nonneg
  have hiR : Rinv * R = 1 := by
    rw [show Rinv * R = spectralPower Y ((-1 / 2) + (1 / 2)) from
      (spectralPower_add Y hY _ _).symm]
    norm_num
    exact CFC.rpow_zero Y hY.isStrictlyPositive.nonneg
  have hRR : R * R = Y := by
    rw [show R * R = spectralPower Y ((1 / 2) + (1 / 2)) from
      (spectralPower_add Y hY _ _).symm]
    norm_num
    exact spectralPower_one Y hY
  have hS : (R * X * R).PosDef := sandwich_posDef X R hX
    (spectralPower_posDef Y hY _)
  have hs : R * (X * Y) * Rinv = R * X * R := by
    rw [← hRR]
    simp only [mul_assoc, hRi, mul_one]
  have hc : (X * Y).charpoly = (R * X * R).charpoly := by
    calc
      (X * Y).charpoly = (X * (R * R)).charpoly := by rw [hRR]
      _ = ((X * R) * R).charpoly := by rw [mul_assoc]
      _ = (R * (X * R)).charpoly := Matrix.charpoly_mul_comm _ _
      _ = (R * X * R).charpoly := by rw [mul_assoc]
  exact ⟨hS, hRi, hiR, hs, hc,
    positive_eigenvalues_of_charpoly_eq hc (ordered_eigenvalues_posDef _ hS)⟩

end NLA.MI23
