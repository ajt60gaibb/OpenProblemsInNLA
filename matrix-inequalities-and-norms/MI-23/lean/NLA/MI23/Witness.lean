/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact positivity and CFC identities for Matthew J. Colbrook's MI-23 witness.
The rational LDL factorization avoids spectral approximation.
-/
import NLA.MI23.FunctionalCalculus
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI23

theorem witnessD_posDef : witnessD.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

theorem witnessPivots_posDef : witnessPivots.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

theorem witnessL_det : witnessL.det = (1 : ℂ) := by
  norm_num [witnessL, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem witnessL_isUnit : IsUnit witnessL := by
  rw [Matrix.isUnit_iff_isUnit_det, witnessL_det]
  exact isUnit_one

theorem witnessT_ldl : witnessT = witnessL * witnessPivots * witnessL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessT, witnessL, witnessPivots, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem witnessT_posDef : witnessT.PosDef := by
  rw [witnessT_ldl]
  exact witnessPivots_posDef.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit witnessL_isUnit)

theorem witnessA_posDef : witnessA.PosDef := naturalPower_posDef _ witnessD_posDef 2

theorem witnessB_posDef : witnessB.PosDef :=
  sandwich_posDef _ _ (naturalPower_posDef _ witnessT_posDef 8) witnessD_posDef

theorem witnessG_posDef : witnessG.PosDef :=
  sandwich_posDef _ _ witnessT_posDef witnessD_posDef

theorem witnessH_posDef : witnessH.PosDef :=
  sandwich_posDef _ _ (naturalPower_posDef _ witnessT_posDef 7) witnessD_posDef

theorem spectralPower_naturalPower {n : ℕ} (A : Mat n) (hA : A.PosDef)
    (k : ℕ) (hk : k ≠ 0) (r : ℝ) :
    spectralPower (A ^ k) r = spectralPower A ((k : ℝ) * r) := by
  rw [← spectralPower_nat A hA k]
  exact CFC.rpow_rpow A (k : ℝ) r (by exact_mod_cast hk) hA.isStrictlyPositive

theorem witnessA_half : spectralPower witnessA (1 / 2) = witnessD := by
  rw [witnessA, spectralPower_naturalPower _ witnessD_posDef 2 (by norm_num)]
  norm_num
  exact spectralPower_one witnessD witnessD_posDef

theorem witnessD_mul_inv : witnessD * witnessDInv = 1 := by
  rw [witnessD, witnessDInv, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem witnessD_inv_mul : witnessDInv * witnessD = 1 := by
  rw [witnessD, witnessDInv, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem witnessA_negative_half : spectralPower witnessA (-1 / 2) = witnessDInv := by
  have h : spectralPower witnessA (-1 / 2) * witnessD = 1 := by
    rw [← witnessA_half, ← spectralPower_add _ witnessA_posDef]
    norm_num
    exact CFC.rpow_zero witnessA witnessA_posDef.isStrictlyPositive.nonneg
  calc
    spectralPower witnessA (-1 / 2) =
        spectralPower witnessA (-1 / 2) * (witnessD * witnessDInv) := by
      rw [witnessD_mul_inv, mul_one]
    _ = witnessDInv := by rw [← mul_assoc, h, one_mul]

theorem witness_normalized_inner :
    spectralPower witnessA (-1 / 2) * witnessB * spectralPower witnessA (-1 / 2) =
      witnessT ^ (8 : ℕ) := by
  rw [witnessA_negative_half, witnessB]
  simp only [← mul_assoc, witnessD_inv_mul, one_mul]
  rw [mul_assoc, witnessD_mul_inv, mul_one]

theorem witnessT_eighth_root : spectralPower (witnessT ^ (8 : ℕ)) (1 / 8) = witnessT := by
  rw [spectralPower_naturalPower _ witnessT_posDef 8 (by norm_num)]
  norm_num
  exact spectralPower_one witnessT witnessT_posDef

theorem witnessT_seven_eighths :
    spectralPower (witnessT ^ (8 : ℕ)) (7 / 8) = witnessT ^ (7 : ℕ) := by
  rw [spectralPower_naturalPower _ witnessT_posDef 8 (by norm_num)]
  norm_num
  exact spectralPower_nat witnessT witnessT_posDef 7

theorem witness_mean_eighth : generalizedMean witnessA witnessB 1 (1 / 8) = witnessG := by
  rw [generalizedMean, witnessA_half, witness_normalized_inner, witnessT_eighth_root]
  rfl

theorem witness_mean_seven_eighths :
    generalizedMean witnessA witnessB 1 (7 / 8) = witnessH := by
  rw [generalizedMean, witnessA_half, witness_normalized_inner, witnessT_seven_eighths]
  rfl

theorem witness_left_product : leftProduct witnessA witnessB 1 1 2 (1 / 8) =
    witnessG ^ (2 : ℕ) * witnessH ^ (2 : ℕ) := by
  unfold leftProduct
  rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, witness_mean_eighth,
    witness_mean_seven_eighths]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl,
    spectralPower_nat _ witnessG_posDef, spectralPower_nat _ witnessH_posDef]

theorem witness_right_product : rightProduct witnessA witnessB 1 1 2 =
    witnessA ^ (2 : ℕ) * witnessB ^ (2 : ℕ) := by
  unfold rightProduct
  rw [show (2 : ℝ) * (1 + 1 - 1) = 2 by norm_num]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl,
    spectralPower_nat _ witnessA_posDef, spectralPower_nat _ witnessB_posDef]

end NLA.MI23
