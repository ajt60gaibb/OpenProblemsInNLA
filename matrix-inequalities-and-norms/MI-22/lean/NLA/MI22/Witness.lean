/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact positivity and principal-power identities for the disclosed rational
adaptation of Matthew J. Colbrook's MI-22 method. The LDL and power proof
organization adapts MI-23, re-proving each identity on this project's matrices.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.MI22.FunctionalCalculus
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI22

theorem witnessD_posDef : witnessD.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

theorem witnessPivots_posDef : witnessPivots.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

theorem witnessLDL_det : witnessLDL.det = (1 : ℂ) := by
  norm_num [witnessLDL, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]

theorem witnessLDL_isUnit : IsUnit witnessLDL := by
  rw [Matrix.isUnit_iff_isUnit_det, witnessLDL_det]
  exact isUnit_one

theorem witnessT_ldl : witnessT = witnessLDL * witnessPivots * witnessLDL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessT, witnessLDL, witnessPivots, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem witnessT_posDef : witnessT.PosDef := by
  rw [witnessT_ldl]
  exact witnessPivots_posDef.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit witnessLDL_isUnit)

theorem witnessA_posDef : witnessA.PosDef := naturalPower_posDef _ witnessD_posDef 2

theorem witnessB_posDef : witnessB.PosDef :=
  sandwich_posDef _ _ (naturalPower_posDef _ witnessT_posDef 8) witnessD_posDef

theorem witnessA_diagonal :
    witnessA = Matrix.diagonal (![256, 1 / 256, 1] : Fin 3 → ℂ) := by
  rw [witnessA, witnessD, pow_two, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> norm_num

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

theorem witnessAOneEighth_posDef : witnessAOneEighth.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

theorem witnessAOneEighth_pow_eight : witnessAOneEighth ^ (8 : ℕ) = witnessA := by
  rw [witnessA_diagonal, witnessAOneEighth, Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> norm_num

theorem witnessA_eighth : spectralPower witnessA (1 / 8) = witnessAOneEighth := by
  rw [← witnessAOneEighth_pow_eight,
    spectralPower_naturalPower _ witnessAOneEighth_posDef 8 (by norm_num)]
  norm_num
  exact spectralPower_one _ witnessAOneEighth_posDef

theorem witnessAOneEighth_pow_five :
    witnessAOneEighth ^ (5 : ℕ) = witnessAFiveEighths := by
  rw [witnessAOneEighth, witnessAFiveEighths, Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> norm_num

theorem witnessA_five_eighths : spectralPower witnessA (5 / 8) = witnessAFiveEighths := by
  rw [← witnessAOneEighth_pow_eight,
    spectralPower_naturalPower _ witnessAOneEighth_posDef 8 (by norm_num)]
  norm_num
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) from rfl,
    spectralPower_nat _ witnessAOneEighth_posDef, witnessAOneEighth_pow_five]

theorem witnessAOneEighth_mul_D : witnessAOneEighth * witnessD = witnessAFiveEighths := by
  rw [witnessAOneEighth, witnessD, witnessAFiveEighths, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> norm_num

theorem witness_normalized_inner : witnessDInv * witnessB * witnessDInv =
    witnessT ^ (8 : ℕ) := by
  rw [witnessB]
  simp only [← mul_assoc, witnessD_inv_mul, one_mul]
  rw [mul_assoc, witnessD_mul_inv, mul_one]

theorem witness_normalized_root :
    spectralPower (witnessDInv * witnessB * witnessDInv) (1 / 8) = witnessT := by
  rw [witness_normalized_inner, spectralPower_naturalPower _ witnessT_posDef 8 (by norm_num)]
  norm_num
  exact spectralPower_one _ witnessT_posDef

theorem witness_weightedMean :
    weightedMean witnessA witnessB (1 / 8) = witnessD * witnessT * witnessD := by
  rw [weightedMean, witnessA_half, witnessA_negative_half, witness_normalized_root]

theorem witnessRoot_posDef : witnessRoot.PosDef :=
  spectralPower_posDef _ witnessB_posDef _

theorem witnessRoot_pow_eight : witnessRoot ^ (8 : ℕ) = witnessB := by
  rw [← spectralPower_nat _ witnessRoot_posDef 8, witnessRoot]
  have h := CFC.rpow_rpow witnessB (1 / 8 : ℝ) (8 : ℝ)
    (by norm_num) witnessB_posDef.isStrictlyPositive
  change spectralPower (spectralPower witnessB (1 / 8)) 8 =
    spectralPower witnessB ((1 / 8) * 8) at h
  norm_num only [Nat.cast_ofNat]
  rw [h]
  norm_num
  exact spectralPower_one _ witnessB_posDef

theorem witnessRoot_right_factor : spectralPower witnessB (7 / 8) * witnessRoot = witnessB := by
  rw [witnessRoot, ← spectralPower_add _ witnessB_posDef]
  norm_num
  exact spectralPower_one _ witnessB_posDef

theorem witness_left_mul_root :
    leftProduct witnessA witnessB (1 / 8) * witnessRoot = witnessN := by
  rw [leftProduct, witnessA_eighth, witness_weightedMean,
    show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, mul_assoc, witnessRoot_right_factor]
  simp only [← mul_assoc, witnessAOneEighth_mul_D, witnessN]

end NLA.MI22
