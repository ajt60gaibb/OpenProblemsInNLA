/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The exact fourth-root norm bound used in Colbrook's IE-23 example. All
root and real-power bridges concern the genuine norms in Definitions.
AI-assisted formalization, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE23.Norms

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

lemma witnessNorm_pos : 0 < witnessNorm := by
  unfold witnessNorm
  positivity

lemma witnessNorm_sq : witnessNorm ^ 2 = Real.sqrt 2 := by
  exact Real.sq_sqrt (Real.sqrt_nonneg 2)

lemma witnessNorm_pow_four : witnessNorm ^ 4 = 2 := by
  calc
    witnessNorm ^ 4 = (witnessNorm ^ 2) ^ 2 := by ring
    _ = (Real.sqrt 2) ^ 2 := by rw [witnessNorm_sq]
    _ = 2 := Real.sq_sqrt (by norm_num)

lemma witnessNorm_rpow : witnessNorm = (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / 4) := by
  unfold witnessNorm
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma lpNorm_fourth_power {n : ℕ} (y : Vec n) :
    lpNorm 4 y ^ (4 : ℕ) = ∑ i, ‖y i‖ ^ (4 : ℕ) := by
  unfold lpNorm
  rw [one_div]
  have h := Real.rpow_inv_natCast_pow
    (x := ∑ i, ‖y i‖ ^ (4 : ℝ))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (n := 4) (by decide)
  simpa only [Nat.cast_ofNat, Real.rpow_ofNat] using h

lemma euclideanNorm_le_four_norm (y : Vec 2) :
    euclideanNorm y ≤ witnessNorm * lpNorm 4 y := by
  have he := euclideanNorm_sq y
  have hl := lpNorm_fourth_power y
  simp only [Fin.sum_univ_two] at he hl
  have hs : euclideanNorm y ^ 4 ≤ 2 * lpNorm 4 y ^ 4 := by
    nlinarith [sq_nonneg (‖y 0‖ ^ 2 - ‖y 1‖ ^ 2)]
  have hs' : (euclideanNorm y ^ 2) ^ 2 ≤ ((witnessNorm * lpNorm 4 y) ^ 2) ^ 2 := by
    calc
      (euclideanNorm y ^ 2) ^ 2 = euclideanNorm y ^ 4 := by ring
      _ ≤ 2 * lpNorm 4 y ^ 4 := hs
      _ = ((witnessNorm * lpNorm 4 y) ^ 2) ^ 2 := by
        rw [← witnessNorm_pow_four]
        ring
  have hs2 := (sq_le_sq₀ (sq_nonneg (euclideanNorm y))
    (sq_nonneg (witnessNorm * lpNorm 4 y))).mp hs'
  exact (sq_le_sq₀ (euclideanNorm_nonneg y)
    (mul_nonneg witnessNorm_pos.le (lpNorm_nonneg _ _))).mp hs2

end NLA.IE23
