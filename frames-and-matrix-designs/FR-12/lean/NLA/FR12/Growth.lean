/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact growth of the labeled Hadamard count. Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena, USA.
AI-assisted formalization; the complete statements were independently approved.
-/
import NLA.FR12.Doubling
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section

namespace NLA.FR12

lemma count_one_pos : 1 ≤ hadamardCount 1 := by
  let A : HadamardMatrices 1 := ⟨1, by
    constructor
    · intro i j
      left
      simp [Matrix.one_apply, Subsingleton.elim i j]
    · norm_num⟩
  let : Nonempty (HadamardMatrices 1) := ⟨A⟩
  exact Nat.card_pos

theorem power_two_nonempty_proved (k : ℕ) : 1 ≤ hadamardCount (2 ^ k) := by
  induction k with
  | zero => simpa using count_one_pos
  | succ k ih =>
    have hm : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    have hf : 1 ≤ (2 ^ k).factorial := Nat.factorial_pos _
    have hs : 1 ≤ hadamardCount (2 ^ k) ^ 2 := one_le_pow₀ ih
    have hprod := Nat.mul_le_mul hf hs
    have hrec := factorial_doubling_proved (2 ^ k) hm
    simpa only [one_mul, pow_succ, Nat.mul_comm] using hprod.trans hrec

/-- Keep the upper half of a factorial. No asymptotic approximation is used. -/
lemma half_factorial_lower_bound (r : ℕ) : r ^ r ≤ (2 * r).factorial := by
  have h := Nat.factorial_mul_pow_sub_le_factorial (show r ≤ 2 * r by omega)
  have he : 2 * r - r = r := by omega
  rw [he] at h
  calc
    r ^ r = 1 * r ^ r := by simp
    _ ≤ r.factorial * r ^ r := Nat.mul_le_mul_right _ (Nat.factorial_pos r)
    _ ≤ (2 * r).factorial := h

lemma factorial_growth (k : ℕ) :
    (2 : ℝ) ^ ((2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1)) ≤
      ((2 ^ (k + 2)).factorial : ℝ) := by
  have h := half_factorial_lower_bound (2 ^ (k + 1))
  have he : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by
    simp only [pow_succ, Nat.mul_comm]
  rw [he] at h
  have hc : ((2 : ℝ) ^ (k + 1)) ^ (2 ^ (k + 1) : ℕ) ≤
      ((2 ^ (k + 2)).factorial : ℝ) := by exact_mod_cast h
  calc
    (2 : ℝ) ^ ((2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1)) =
        ((2 : ℝ) ^ (k + 1)) ^ (2 ^ (k + 1) : ℕ) := by
      rw [mul_comm, show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by simp,
        Real.rpow_natCast_mul (by norm_num)]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (Real.rpow_natCast ((2 : ℝ) ^ (k + 1)) (2 ^ (k + 1)))
    _ ≤ _ := hc

theorem power_two_lower_bound_proved (k : ℕ) :
    (2 : ℝ) ^ ((2 : ℝ) ^ (k + 2) * (k : ℝ) * ((k : ℝ) + 1) / 8) ≤
      (hadamardCount (2 ^ (k + 2)) : ℝ) := by
  induction k with
  | zero =>
    norm_num only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.rpow_zero]
    exact_mod_cast power_two_nonempty_proved 2
  | succ k ih =>
    have hm : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
    have hrec := factorial_doubling_proved (2 ^ (k + 2)) hm
    have he : 2 * 2 ^ (k + 2) = 2 ^ (k + 3) := by
      simp only [pow_succ, Nat.mul_comm]
    rw [he] at hrec
    have hc : ((2 ^ (k + 2)).factorial : ℝ) *
        (hadamardCount (2 ^ (k + 2)) : ℝ) ^ 2 ≤
        (hadamardCount (2 ^ (k + 3)) : ℝ) := by exact_mod_cast hrec
    have hs := mul_self_le_mul_self (by positivity :
        0 ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (k + 2) * (k : ℝ) * ((k : ℝ) + 1) / 8)) ih
    rw [← sq, ← sq] at hs
    have hp := mul_le_mul (factorial_growth k) hs (by positivity) (by positivity)
    have hexp : (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) +
        ((2 : ℝ) ^ (k + 2) * (k : ℝ) * ((k : ℝ) + 1) / 8) * 2 =
        (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 1) * ((k : ℝ) + 2) / 8 := by
      simp only [pow_succ]
      ring
    have hidentity : (2 : ℝ) ^ ((2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1)) *
        ((2 : ℝ) ^ ((2 : ℝ) ^ (k + 2) * (k : ℝ) * ((k : ℝ) + 1) / 8)) ^ 2 =
        (2 : ℝ) ^ ((2 : ℝ) ^ (k + 3) * ((k : ℝ) + 1) * ((k : ℝ) + 2) / 8) := by
      rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_add (by norm_num)]
      exact congrArg (fun x : ℝ => (2 : ℝ) ^ x) hexp
    rw [hidentity] at hp
    simpa [Nat.add_assoc, add_assoc, one_add_one_eq_two] using hp.trans hc

lemma log_power_two (k : ℕ) :
    Real.log ((2 ^ (k + 2) : ℕ) : ℝ) / Real.log 2 = (k : ℝ) + 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have h : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  push_cast
  ring

theorem counterexample_proved (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ,
      (2 : ℝ) ^ (C * ((2 ^ (k + 2) : ℕ) : ℝ) *
        (Real.log ((2 ^ (k + 2) : ℕ) : ℝ) / Real.log 2)) <
          (hadamardCount (2 ^ (k + 2)) : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (16 * C + 2)
  have hpoly : C * ((k : ℝ) + 2) < (k : ℝ) * ((k : ℝ) + 1) / 8 := by
    nlinarith [mul_pos (sub_pos.mpr hk) (by positivity : 0 < (k : ℝ) + 2),
      mul_nonneg hC.le (Nat.cast_nonneg k)]
  have hn : 0 < (2 : ℝ) ^ (k + 2) := by positivity
  have hexp : C * ((2 ^ (k + 2) : ℕ) : ℝ) *
        (Real.log ((2 ^ (k + 2) : ℕ) : ℝ) / Real.log 2) <
      (2 : ℝ) ^ (k + 2) * (k : ℝ) * ((k : ℝ) + 1) / 8 := by
    calc
      _ = (2 : ℝ) ^ (k + 2) * (C * ((k : ℝ) + 2)) := by
        rw [log_power_two]
        push_cast
        ring
      _ < (2 : ℝ) ^ (k + 2) * ((k : ℝ) * ((k : ℝ) + 1) / 8) :=
        mul_lt_mul_of_pos_left hpoly hn
      _ = _ := by ring
  exact ⟨k, (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp).trans_le
    (power_two_lower_bound_proved k)⟩

theorem not_countingConjecture_proved : ¬ CountingConjecture := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨k, hk⟩ := counterexample_proved C hC
  have hn : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
  have hd : 4 ∣ 2 ^ (k + 2) := by
    use 2 ^ k
    simp [pow_add, Nat.mul_comm]
  exact (not_le_of_gt hk) (hbound (2 ^ (k + 2)) hn hd)

end NLA.FR12
