/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The lower binomial estimate is proved by a finite descending-factorial
comparison. No asymptotic estimate or numerical factorial evaluation is used.
-/
import NLA.MF12.JordanEntries
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF12

lemma scaled_descFactorial_le (n m : ℕ) (hmn : m ≤ n) (k : ℕ) (hkm : k ≤ m) :
    n ^ k * m.descFactorial k ≤ m ^ k * n.descFactorial k := by
  revert hkm
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hkm
      have hkm' : k ≤ m := by omega
      have hkn : k ≤ n := hkm'.trans hmn
      have hfactor : n * (m - k) ≤ m * (n - k) := by
        have hm := Nat.sub_add_cancel hkm'
        have hn := Nat.sub_add_cancel hkn
        have hmul := Nat.mul_le_mul_right k hmn
        nlinarith
      rw [pow_succ, pow_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
      calc
        n ^ k * n * ((m - k) * m.descFactorial k) =
            (n ^ k * m.descFactorial k) * (n * (m - k)) := by ring
        _ ≤ (m ^ k * n.descFactorial k) * (m * (n - k)) :=
          Nat.mul_le_mul (ih hkm') hfactor
        _ = m ^ k * m * ((n - k) * n.descFactorial k) := by ring

lemma pow_le_scaled_choose (n m : ℕ) (hmn : m ≤ n) :
    n ^ m ≤ m ^ m * n.choose m := by
  apply Nat.le_of_mul_le_mul_right (c := m.factorial) _ (Nat.factorial_pos m)
  simpa only [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      scaled_descFactorial_le n m hmn m le_rfl

lemma jordanLower_pos (m : ℕ) : 0 < jordanLower m := by
  by_cases hm : m = 0
  · simp [jordanLower, hm]
  · have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    simpa only [jordanLower, if_neg hm] using inv_pos.mpr (pow_pos hmR m)

lemma jordan_power_norm_ge_one (m n : ℕ) : 1 ≤ spectralNorm (jordanMatrix m ^ n) := by
  have h := abs_entry_le_spectralNorm (jordanMatrix m ^ n) 0 0
  simpa only [jordan_power_diagonal, abs_one] using h

lemma jordan_norm_lower (m n : ℕ) :
    jordanLower m * (n : ℝ) ^ m ≤ spectralNorm (jordanMatrix m ^ n) := by
  by_cases hm : m = 0
  · simpa only [hm, jordanLower, if_pos rfl, pow_zero, mul_one] using
      jordan_power_norm_ge_one 0 n
  · have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hpow : 0 < (m : ℝ) ^ m := pow_pos hmR m
    by_cases hmn : m ≤ n
    · have hchoose : (n : ℝ) ^ m ≤ (m : ℝ) ^ m * (n.choose m : ℝ) := by
        exact_mod_cast pow_le_scaled_choose n m hmn
      have hentry := abs_entry_le_spectralNorm (jordanMatrix m ^ n)
        (0 : Fin (m + 1)) ⟨m, by omega⟩
      have hchooseNorm : (n.choose m : ℝ) ≤ spectralNorm (jordanMatrix m ^ n) := by
        simpa only [jordan_entries, Fin.val_zero, Fin.val_mk, Nat.zero_le,
          if_pos, Nat.sub_zero, abs_of_nonneg (Nat.cast_nonneg _)] using hentry
      calc
        jordanLower m * (n : ℝ) ^ m = (n : ℝ) ^ m / (m : ℝ) ^ m := by
          rw [jordanLower, if_neg hm, div_eq_mul_inv, mul_comm]
        _ ≤ (n.choose m : ℝ) := (div_le_iff₀ hpow).mpr (by simpa only [mul_comm] using hchoose)
        _ ≤ spectralNorm (jordanMatrix m ^ n) := hchooseNorm
    · have hnm : n ≤ m := by omega
      have hle : (n : ℝ) ^ m ≤ (m : ℝ) ^ m := by
        exact_mod_cast Nat.pow_le_pow_left hnm m
      calc
        jordanLower m * (n : ℝ) ^ m = (n : ℝ) ^ m / (m : ℝ) ^ m := by
          rw [jordanLower, if_neg hm, div_eq_mul_inv, mul_comm]
        _ ≤ 1 := (div_le_iff₀ hpow).mpr (by simpa only [one_mul] using hle)
        _ ≤ spectralNorm (jordanMatrix m ^ n) := jordan_power_norm_ge_one m n

lemma jordan_norm_upper (m n : ℕ) (hn : 1 ≤ n) :
    spectralNorm (jordanMatrix m ^ n) ≤ ((m + 1 : ℕ) : ℝ) * (n : ℝ) ^ m := by
  apply spectralNorm_le_entry_bound _ _ (pow_nonneg (Nat.cast_nonneg n) m)
  intro r s
  rw [jordan_entries]
  by_cases hrs : r.val ≤ s.val
  · rw [if_pos hrs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hdegree : s.val - r.val ≤ m := by omega
    have hNat := (Nat.choose_le_pow n (s.val - r.val)).trans
      (Nat.pow_le_pow_right (by omega : 0 < n) hdegree)
    exact_mod_cast hNat
  · rw [if_neg hrs, abs_zero]
    exact pow_nonneg (Nat.cast_nonneg n) m

theorem jordan_growth_estimates (m : ℕ) :
    0 < jordanLower m ∧ jordanMatrix m ≠ 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      jordanLower m * (n : ℝ) ^ m ≤ spectralNorm (jordanMatrix m ^ n) ∧
      spectralNorm (jordanMatrix m ^ n) ≤ ((m + 1 : ℕ) : ℝ) * (n : ℝ) ^ m := by
  exact ⟨jordanLower_pos m, jordanMatrix_ne_zero m,
    fun n hn => ⟨jordan_norm_lower m n, jordan_norm_upper m n hn⟩⟩

#assert_trust kernel jordan_growth_estimates
#print axioms jordan_growth_estimates

end NLA.MF12
