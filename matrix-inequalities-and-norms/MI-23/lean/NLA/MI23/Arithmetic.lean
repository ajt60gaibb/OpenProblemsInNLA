/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact repeated-squaring certificates for Colbrook's MI-23 witness.
Only the single rational point separation uses LeanCert; all matrix identities
are checked by ordinary kernel arithmetic.
-/
import NLA.MI23.Witness
import NLA.MI23.NormBounds
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI23

private def certificateT2 : Mat 3 :=
  !![9, 7, 14;
     7, 726, -348;
     14, -348, 204]

private def certificateT4 : Mat 3 :=
  !![326, 273, 546;
     273, 648229, -323542;
     546, -323542, 162916]

private def certificateT7 : Mat 3 :=
  !![77338, 64849, 129698;
     64849, 17496054377, -8747891246;
     129698, -8747891246, 4374217508]

private def certificateT8 : Mat 3 :=
  !![478921, 401583, 803166;
     401583, 524880336734, -262439326532;
     803166, -262439326532, 131221346936]

private def certificateB : Mat 3 :=
  !![122603776, 535444, 12850656;
     535444, 262440168367 / 72, -65609831633 / 3;
     12850656, -65609831633 / 3, 131221346936]

private def certificateG : Mat 3 :=
  !![512, 4 / 3, 32;
     4 / 3, 25 / 144, -5 / 6;
     32, -5 / 6, 10]

private def certificateH : Mat 3 :=
  !![19798528, 259396 / 3, 2075168;
     259396 / 3, 17496054377 / 144, -4373945623 / 6;
     2075168, -4373945623 / 6, 4374217508]

private theorem power_two_certificate : witnessT ^ (2 : ℕ) = certificateT2 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessT, certificateT2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem power_four_certificate : witnessT ^ (4 : ℕ) = certificateT4 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, power_two_certificate, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [certificateT2, certificateT4, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem power_seven_certificate : witnessT ^ (7 : ℕ) = certificateT7 := by
  rw [show (7 : ℕ) = (4 + 2) + 1 by rfl, pow_add, pow_add, pow_one,
    power_four_certificate, power_two_certificate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessT, certificateT2, certificateT4, certificateT7, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

private theorem power_eight_certificate : witnessT ^ (8 : ℕ) = certificateT8 := by
  rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, power_four_certificate, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [certificateT4, certificateT8, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem witnessB_certificate : witnessB = certificateB := by
  rw [witnessB, power_eight_certificate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessD, certificateT8, certificateB, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

private theorem witnessG_certificate : witnessG = certificateG := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessG, witnessD, witnessT, certificateG, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem witnessH_certificate : witnessH = certificateH := by
  rw [witnessH, power_seven_certificate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessD, certificateT7, certificateH, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem witness_GH_entry : (witnessG * witnessH) 0 2 = (1260589125202 / 9 : ℂ) := by
  rw [witnessG_certificate, witnessH_certificate]
  norm_num [certificateG, certificateH, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem witness_frobenius_AB : frobeniusSquared (witnessA * witnessB) =
    (2009446159144992718181231562721 / 107495424 : ℝ) := by
  rw [witnessB_certificate, witnessA, witnessD, Matrix.diagonal_pow]
  norm_num [frobeniusSquared, certificateB, Matrix.mul_apply, Matrix.diagonal_apply,
    Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem witness_exact_gap : Complex.normSq ((witnessG * witnessH) 0 2) -
    frobeniusSquared (witnessA * witnessB) = squaredGap := by
  rw [witness_GH_entry, witness_frobenius_AB]
  norm_num [squaredGap, Complex.normSq_apply, Complex.div_re, Complex.div_im]

/-- A single explicit-kernel LeanCert point certificate; no eigenvalue intervals. -/
theorem scalar_gap_positive : (0 : ℝ) < 99434824489435745411095588895 / 107495424 := by
  interval_decide (trust := kernel)

theorem squaredGap_positive : 0 < squaredGap := scalar_gap_positive

theorem witness_strict_norm_gap : operatorNorm (witnessA * witnessB) ^ 2 <
    operatorNorm (witnessG * witnessH) ^ 2 := by
  have hleft := operatorNorm_sq_le_frobeniusSquared (witnessA * witnessB)
  have hright := (operator_norm_bounds_proved (witnessG * witnessH) 0 2).1
  have hgap := squaredGap_positive
  rw [← witness_exact_gap] at hgap
  linarith

end NLA.MI23
