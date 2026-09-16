/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The exact lower word is reduced to a two-dimensional geometric identity.
Two actual matrix entries suffice for the norm bound; no interval, square-root
approximation, or asymptotic replacement of the floor is required.
-/
import NLA.MF12.GapBounds
import NLA.MF12.Upper
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.MF12

lemma triangular_geometric_power (ell b : ℝ) (hell : ell ≠ 0) (k : ℕ) :
    (!![1 - ell, b; 0, 1] : Square 2) ^ k =
      !![(1 - ell) ^ k, b / ell * (1 - (1 - ell) ^ k); 0, 1] := by
  induction k with
  | zero =>
      ext r s
      fin_cases r <;> fin_cases s <;> norm_num [Matrix.one_apply]
  | succ k ih =>
      rw [pow_succ, ih]
      ext r s
      fin_cases r <;> fin_cases s
      all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
      · change (1 - ell) ^ k * (1 - ell) +
          (b / ell * (1 - (1 - ell) ^ k)) * 0 = (1 - ell) ^ (k + 1)
        simp only [mul_zero, add_zero, pow_succ]
      · change (1 - ell) ^ k * b + (b / ell * (1 - (1 - ell) ^ k)) * 1 =
          b / ell * (1 - (1 - ell) ^ (k + 1))
        rw [pow_succ]
        field_simp [hell]
        ring
      · change (0 : ℝ) * (1 - ell) + 1 * 0 = 0
        ring
      · change (0 : ℝ) * b + 1 * 1 = 1
        ring

lemma reset_repeat_mul_V (α : ℝ) (q k : ℕ) :
    (resetMatrix * fractionalMatrix α ^ q) ^ k * sourceV =
      sourceV * compressed α q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, pow_succ']
      simp only [resetMatrix, compressed, Matrix.mul_assoc]

lemma padded_repeat_compressed_entry (α : ℝ) (q k r : ℕ) :
    ((fractionalMatrix α ^ r * (resetMatrix * fractionalMatrix α ^ q) ^ k) *
      sourceV) 0 1 = (compressed α q ^ k) 0 1 := by
  rw [Matrix.mul_assoc, reset_repeat_mul_V, ← Matrix.mul_assoc,
    fractionalMatrix_power, fractionalPowerForm_mul_V, Matrix.mul_apply, Fin.sum_univ_two]
  change 1 * (compressed α q ^ k) 0 1 + 0 * (compressed α q ^ k) 1 1 = _
  ring

lemma mul_sourceV_entry_le_norm (B : Square 6) :
    (B * sourceV) 0 1 ≤ 2 * spectralNorm B := by
  have h4 := abs_entry_le_spectralNorm B 0 4
  have h5 := abs_entry_le_spectralNorm B 0 5
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  change B 0 0 * 0 + B 0 1 * 0 + B 0 2 * 0 + B 0 3 * 0 +
    B 0 4 * 1 + B 0 5 * 1 ≤ _
  simp only [mul_zero, zero_add, mul_one]
  linarith [le_abs_self (B 0 4), le_abs_self (B 0 5)]

lemma gain_div_loss (α : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    gain α q / loss q = ((4 : ℝ) ^ q) ^ α := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have hp : 0 < baseLambda ^ q := pow_pos baseLambda_pos q
  calc
    gain α q / loss q = (baseLambda ^ q) ^ (1 - α) / (baseLambda ^ q) := by
      unfold gain loss baseMu
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_pow_comm baseLambda_pos.le]
      field_simp [hqR, hp.ne']
    _ = (baseLambda ^ q) ^ ((1 - α) - 1) :=
      (Real.rpow_sub_one hp.ne' (1 - α)).symm
    _ = ((baseLambda ^ q)⁻¹) ^ α := by
      rw [show (1 - α) - 1 = -α by ring, Real.rpow_neg_eq_inv_rpow]
    _ = ((4 : ℝ) ^ q) ^ α := by
      rw [baseLambda, div_pow, one_pow, one_div, inv_inv]

lemma chosen_gain_ratio_lower (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 4 ≤ n) :
    baseLambda ^ α * (n : ℝ) ^ α ≤ gain α (chosenGap n) / loss (chosenGap n) := by
  have hgap := logarithmic_gap_bounds n hn
  have hnext : (n : ℝ) < (4 : ℝ) ^ (chosenGap n + 1) := by exact_mod_cast hgap.2.2.2.1
  have hbase : baseLambda * (n : ℝ) ≤ (4 : ℝ) ^ chosenGap n := by
    rw [pow_succ] at hnext
    norm_num only [baseLambda]
    nlinarith
  rw [gain_div_loss α (chosenGap n) hgap.1]
  rw [← Real.mul_rpow baseLambda_pos.le (Nat.cast_nonneg n)]
  exact Real.rpow_le_rpow (mul_nonneg baseLambda_pos.le (Nat.cast_nonneg n)) hbase hα.le

lemma fractional_power_norm_ge_one (α : ℝ) (n : ℕ) :
    1 ≤ spectralNorm (fractionalMatrix α ^ n) := by
  have h := abs_entry_le_spectralNorm (fractionalMatrix α ^ n) 0 0
  rw [fractionalMatrix_power] at h
  change |(1 : ℝ)| ≤ spectralNorm (fractionalPowerForm α n) at h
  simpa only [abs_one, fractionalMatrix_power] using h

theorem fractional_lower_all_lengths (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    fractionalLower α * Real.rpow (n : ℝ) α ≤
      spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix (lowerWord n)) := by
  rw [(lower_word_exact α n).2]
  by_cases hn4 : n < 4
  · rw [if_pos hn4]
    have hsmall : baseLambda * (n : ℝ) ≤ 1 := by
      have hnR : (n : ℝ) ≤ 3 := by exact_mod_cast (show n ≤ 3 by omega)
      norm_num only [baseLambda]
      nlinarith
    have hpow := Real.rpow_le_rpow
      (mul_nonneg baseLambda_pos.le (Nat.cast_nonneg n)) hsmall hα.le
    rw [Real.mul_rpow baseLambda_pos.le (Nat.cast_nonneg n), Real.one_rpow] at hpow
    have hnorm := fractional_power_norm_ge_one α n
    change baseLambda ^ α / 10 * (n : ℝ) ^ α ≤ _
    nlinarith
  · rw [if_neg hn4]
    have hn4' : 4 ≤ n := by omega
    have hg := logarithmic_gap_bounds n hn4'
    let q := chosenGap n
    let k := chosenCount n
    let r := chosenRemainder n
    have hell : 0 < loss q := loss_pos q hg.1
    have hmass : (1 / 4 : ℝ) ≤ (k : ℝ) * loss q := hg.2.2.2.2.2.2
    have hdecay : (1 / 5 : ℝ) ≤ 1 - (1 - loss q) ^ k :=
      (bernoulli_loss (loss q) hell.le (loss_lt_one q) k).2 hmass
    have hratio0 : 0 ≤ gain α q / loss q := by
      rw [gain_div_loss α q hg.1]
      exact Real.rpow_nonneg (by positivity) _
    have hentry := mul_sourceV_entry_le_norm
      (fractionalMatrix α ^ r * (resetMatrix * fractionalMatrix α ^ q) ^ k)
    rw [padded_repeat_compressed_entry, compressed_powers,
      triangular_geometric_power (loss q) (gain α q) hell.ne'] at hentry
    change gain α q / loss q * (1 - (1 - loss q) ^ k) ≤
      2 * spectralNorm (fractionalMatrix α ^ r * (resetMatrix * fractionalMatrix α ^ q) ^ k)
      at hentry
    have hproduct := mul_le_mul_of_nonneg_left hdecay hratio0
    have hscale : baseLambda ^ α * (n : ℝ) ^ α ≤ gain α q / loss q :=
      chosen_gain_ratio_lower α hα n hn4'
    change baseLambda ^ α / 10 * (n : ℝ) ^ α ≤
      spectralNorm (fractionalMatrix α ^ r * (resetMatrix * fractionalMatrix α ^ q) ^ k)
    nlinarith

theorem fractional_growth_estimates (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    fractionalLower α * Real.rpow (n : ℝ) α ≤
      familyGrowth (pairFamily (fractionalMatrix α) resetMatrix) n ∧
    familyGrowth (pairFamily (fractionalMatrix α) resetMatrix) n ≤
      fractionalUpper α * Real.rpow (n : ℝ) α := by
  constructor
  · have h := binaryProduct_le_familyGrowth (fractionalMatrix α) resetMatrix (lowerWord n)
    rw [(lower_word_exact α n).1] at h
    exact (fractional_lower_all_lengths α hα hα1 n hn).trans h
  · apply familyGrowth_le_of_binary
    intro w hw
    have h := fractional_all_word_upper α hα hα1 w (by omega)
    simpa only [hw] using h

#assert_trust kernel fractional_lower_all_lengths
#assert_trust kernel fractional_growth_estimates
#print axioms fractional_lower_all_lengths
#print axioms fractional_growth_estimates

end NLA.MF12
