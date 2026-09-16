/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
This proves the actual root limit; no spectral-radius value is assigned by definition.
-/
import NLA.MF12.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter

namespace NLA.MF12

lemma polynomial_model_root_limit (c γ : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.rpow (c * Real.rpow (n : ℝ) γ) (1 / (n : ℝ)))
      atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 / (n : ℝ))) atTop (𝓝 1) :=
    _root_.tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => Real.rpow (Real.rpow (n : ℝ) (1 / (n : ℝ))) γ)
      atTop (𝓝 1) := by
    simpa only [Real.rpow_eq_pow, Real.one_rpow] using hbase.rpow_const (Or.inl one_ne_zero)
  have hconst : Tendsto (fun n : ℕ => Real.rpow c (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).rpow
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0)) (Or.inl hc.ne')
    simpa only [Real.rpow_eq_pow, Real.rpow_zero] using h
  have hprod : Tendsto (fun n : ℕ => Real.rpow c (1 / (n : ℝ)) *
      Real.rpow (Real.rpow (n : ℝ) (1 / (n : ℝ))) γ) atTop (𝓝 1) := by
    simpa only [one_mul] using hconst.mul hpow
  apply hprod.congr'
  filter_upwards [] with n
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg n) γ),
    ← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_mul (Nat.cast_nonneg n),
    mul_comm γ (1 / (n : ℝ))]

theorem roots_of_polynomial_growth (g : ℕ → ℝ) (γ c C : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hC : 0 < C)
    (hg : ∀ n : ℕ, 1 ≤ n →
      c * Real.rpow (n : ℝ) γ ≤ g n ∧ g n ≤ C * Real.rpow (n : ℝ) γ) :
    Tendsto (fun n : ℕ => Real.rpow (g n) (1 / (n : ℝ))) atTop (𝓝 1) := by
  apply (polynomial_model_root_limit c γ hc).squeeze'
    (polynomial_model_root_limit C γ hC)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.rpow_le_rpow
      (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg n) γ)) (hg n hn).1
      (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hgn : 0 ≤ g n := (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg n) γ)).trans
      (hg n hn).1
    exact Real.rpow_le_rpow hgn (hg n hn).2 (by positivity)

#assert_trust kernel roots_of_polynomial_growth
#print axioms roots_of_polynomial_growth

end NLA.MF12
