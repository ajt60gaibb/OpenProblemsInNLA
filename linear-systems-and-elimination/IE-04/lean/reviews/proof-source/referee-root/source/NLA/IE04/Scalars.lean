/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.IE04.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.IE04

theorem scalar_budgets {n : ℕ} (hn : 2 ≤ n) :
    0 < boxRadius n ∧ boxRadius n ≤ 1 / 8 ∧
      stageAmplification n ^ (n - 1) * boxRadius n = 1 / 8 ∧
      ∀ k : ℕ, k < n →
        stageAmplification n ^ k * boxRadius n ≤ 1 / 8 ∧
          1 ≤ (3 / 2 : ℝ) ^ k ∧ (3 / 2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
  have hδ : 0 < boxRadius n := by unfold boxRadius; positivity
  have hL : 1 ≤ stageAmplification n := by
    unfold stageAmplification
    exact one_le_pow₀ (by norm_num)
  have hexponent : n ^ 2 + n + 1 = (n + 2) * (n - 1) + 3 := by
    cases n with
    | zero => omega
    | succ n =>
        simp only [Nat.add_sub_cancel]
        ring
  have hbudget : stageAmplification n ^ (n - 1) * boxRadius n = 1 / 8 := by
    unfold stageAmplification boxRadius
    rw [hexponent, pow_add (2 : ℝ) ((n + 2) * (n - 1)) 3,
      pow_mul (2 : ℝ) (n + 2) (n - 1)]
    norm_num
    field_simp
  have hδsmall : boxRadius n ≤ 1 / 8 := by
    calc
      boxRadius n ≤ stageAmplification n ^ (n - 1) * boxRadius n := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (one_le_pow₀ hL (n := n - 1)) hδ.le
      _ = 1 / 8 := hbudget
  refine ⟨hδ, hδsmall, hbudget, ?_⟩
  intro k hk
  refine ⟨?_, one_le_pow₀ (by norm_num), ?_⟩
  · calc
      stageAmplification n ^ k * boxRadius n ≤
          stageAmplification n ^ (n - 1) * boxRadius n :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hL (by omega)) hδ.le
      _ = 1 / 8 := hbudget
  · calc
      (3 / 2 : ℝ) ^ k ≤ (2 : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) k
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hk)

theorem quotient_bounds (e p a : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 8)
    (hp : |p - 1| ≤ e) (ha : |a + 1 / 2| ≤ e) :
    7 / 8 ≤ p ∧ |a| ≤ 5 / 8 ∧ |a / p| ≤ 5 / 7 ∧
      |a / p + 1 / 2| ≤ 2 * e := by
  have hp' := abs_le.mp hp
  have ha' := abs_le.mp ha
  have hpbound : (7 : ℝ) / 8 ≤ p := by linarith
  have hppos : 0 < p := by linarith
  have habound : |a| ≤ (5 : ℝ) / 8 := by
    rw [abs_le]
    constructor <;> linarith
  have hratio : |a / p| ≤ (5 : ℝ) / 7 := by
    rw [abs_div, abs_of_pos hppos, div_le_iff₀ hppos]
    linarith
  refine ⟨hpbound, habound, hratio, ?_⟩
  have hnum : |(a + 1 / 2) + (p - 1) / 2| ≤ e + e / 2 := by
    calc
      |(a + 1 / 2) + (p - 1) / 2| ≤ |a + 1 / 2| + |(p - 1) / 2| :=
        abs_add_le _ _
      _ ≤ e + e / 2 := add_le_add ha (by
        simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          div_le_div_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 2))
  have hid : a / p + 1 / 2 = ((a + 1 / 2) + (p - 1) / 2) / p := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hppos]
  calc
    |(a + 1 / 2) + (p - 1) / 2| / p ≤ (e + e / 2) / p :=
      div_le_div_of_nonneg_right hnum hppos.le
    _ ≤ 2 * e := (div_le_iff₀ hppos).mpr (by nlinarith)

theorem scalar_schur_error (n : ℕ) (e p a u u₀ v v₀ : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1 / 8) (hp : |p - 1| ≤ e)
    (ha : |a + 1 / 2| ≤ e) (hu : |u - u₀| ≤ e) (hv : |v - v₀| ≤ e)
    (hv₀ : |v₀| ≤ (2 : ℝ) ^ n) :
    |(u - (a / p) * v) - (u₀ + v₀ / 2)| ≤ stageAmplification n * e := by
  obtain ⟨_, _, hratio, hnear⟩ := quotient_bounds e p a he he' hp ha
  have htwo : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hetwo : e ≤ (2 : ℝ) ^ n * e := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo he
  calc
    |(u - (a / p) * v) - (u₀ + v₀ / 2)| =
        |((u - u₀) + (-(a / p)) * (v - v₀)) + (-(a / p + 1 / 2)) * v₀| := by
      congr 1
      ring
    _ ≤ |(u - u₀) + (-(a / p)) * (v - v₀)| + |(-(a / p + 1 / 2)) * v₀| :=
      abs_add_le _ _
    _ ≤ (|u - u₀| + |(-(a / p)) * (v - v₀)|) + |(-(a / p + 1 / 2)) * v₀| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |u - u₀| + |a / p| * |v - v₀| + |a / p + 1 / 2| * |v₀| := by
      simp only [abs_mul, abs_neg]
    _ ≤ e + (5 / 7 : ℝ) * e + (2 * e) * (2 : ℝ) ^ n := by
      apply add_le_add
      · exact add_le_add hu
          (mul_le_mul hratio hv (abs_nonneg _) (by norm_num))
      · exact mul_le_mul hnear hv₀ (abs_nonneg _) (by positivity)
    _ ≤ stageAmplification n * e := by
      simp only [stageAmplification, pow_add]
      norm_num
      nlinarith

#assert_trust kernel scalar_budgets
#assert_trust kernel quotient_bounds
#assert_trust kernel scalar_schur_error
#print axioms scalar_budgets
#print axioms quotient_bounds
#print axioms scalar_schur_error

end NLA.IE04
