/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exponential domination chooses a finite violating dimension for arbitrary
positive real tail constants. No enormous explicit dimension or numerical
search is used, and both constants retain their complete real quantifiers.
-/
import NLA.IE04.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter
noncomputable section
namespace NLA.IE04

theorem exponential_ratio_tendsto (s : ℝ) :
    Tendsto (fun n : ℕ => (3 / 2 : ℝ) ^ n / (n : ℝ) ^ s) atTop atTop := by
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have h := (Real.tendsto_exp_mul_div_rpow_atTop s (Real.log (3 / 2)) hlog).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hexp (n : ℕ) : Real.exp (Real.log (3 / 2 : ℝ) * (n : ℝ)) = (3 / 2 : ℝ) ^ n := by
    rw [Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2), Real.rpow_natCast]
  simpa only [Function.comp_def, hexp] using h

theorem threshold_ratio_identity {n : ℕ} (hn : 1 ≤ n) (c₁ : ℝ) :
    (3 / 2 : ℝ) ^ n / (n : ℝ) ^ (c₁ + 4) =
      3 * contradictionThreshold n c₁ / (n : ℝ) ^ 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (3 / 2 : ℝ) ^ n = (3 / 2 : ℝ) ^ (n - 1) * (3 / 2 : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hpower : (n : ℝ) ^ c₁ ≠ 0 := (Real.rpow_pos_of_pos hnpos c₁).ne'
  rw [hp, Real.rpow_add hnpos c₁ 4, Real.rpow_ofNat]
  unfold contradictionThreshold
  field_simp
  ring

theorem probabilityExponent_quartic {n : ℕ} (hn : 2 ≤ n) :
    (probabilityExponent n : ℝ) ≤ 3 * (n : ℝ) ^ 4 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hinner : (n : ℝ) ^ 2 + (n : ℝ) + 5 ≤ 3 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hmul := mul_le_mul_of_nonneg_left hinner (sq_nonneg (n : ℝ))
  simp only [probabilityExponent, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

theorem contradiction_dimension (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ n : ℕ, 2 ≤ n ∧ 1 ≤ contradictionThreshold n c₁ ∧
      (probabilityExponent n : ℝ) < c₂ * contradictionThreshold n c₁ := by
  let f : ℕ → ℝ := fun n => (3 / 2 : ℝ) ^ n / (n : ℝ) ^ (c₁ + 4)
  have hf : Tendsto f atTop atTop := exponential_ratio_tendsto (c₁ + 4)
  have hlarge : ∀ᶠ n in atTop, max (9 / c₂) 3 < f n :=
    hf.eventually (eventually_gt_atTop _)
  obtain ⟨n, hn, hfn⟩ := ((eventually_ge_atTop (2 : ℕ)).and hlarge).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn4pos : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
  have hratio : f n = 3 * contradictionThreshold n c₁ / (n : ℝ) ^ 4 :=
    threshold_ratio_identity (by omega) c₁
  have hratio_mul : f n * (n : ℝ) ^ 4 = 3 * contradictionThreshold n c₁ := by
    rw [hratio]
    field_simp
  have hthree : (3 : ℝ) < f n := (le_max_right _ _).trans_lt hfn
  have hx : 1 ≤ contradictionThreshold n c₁ := by
    have h := mul_lt_mul_of_pos_right hthree hn4pos
    rw [hratio_mul] at h
    linarith
  have hnine : 9 / c₂ < f n := (le_max_left _ _).trans_lt hfn
  have hnine' : (9 : ℝ) < f n * c₂ := (div_lt_iff₀ hc₂).mp hnine
  have hcross : 9 * (n : ℝ) ^ 4 < 3 * contradictionThreshold n c₁ * c₂ := by
    calc
      9 * (n : ℝ) ^ 4 < (f n * c₂) * (n : ℝ) ^ 4 :=
        mul_lt_mul_of_pos_right hnine' hn4pos
      _ = (f n * (n : ℝ) ^ 4) * c₂ := by ring
      _ = 3 * contradictionThreshold n c₁ * c₂ := by rw [hratio_mul]
  refine ⟨n, hn, hx, ?_⟩
  have hexponent := probabilityExponent_quartic hn
  nlinarith

#assert_trust kernel contradiction_dimension
#print axioms contradiction_dimension

end NLA.IE04
