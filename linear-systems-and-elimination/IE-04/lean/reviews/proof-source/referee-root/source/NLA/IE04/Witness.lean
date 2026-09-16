/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exact symbolic stages of the source matrix, with actual GEPP and its full
finite maximum. No dimension-specific evaluation or interval enumeration.
-/
import NLA.IE04.StrictPivots
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal
noncomputable section
namespace NLA.IE04

theorem modelStage_zero (n : ℕ) : modelStage n 0 = witnessMatrix n := by
  ext i j
  simp [modelStage, witnessMatrix]

theorem modelStage_pivot {n k : ℕ} (hk : k < n) :
    modelStage n k ⟨k, hk⟩ ⟨k, hk⟩ =
      if k + 1 = n then (3 / 2 : ℝ) ^ k else 1 := by
  simp [modelStage]

theorem modelStage_lower_pivot {n k : ℕ} (hk : k < n) (hk' : k + 1 < n)
    (i : Fin n) (hi : k < i.val) : modelStage n k i ⟨k, hk⟩ = -(1 / 2 : ℝ) := by
  have hlast : k + 1 ≠ n := by omega
  have hne : i ≠ (⟨k, hk⟩ : Fin n) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  simp [modelStage, hi.le, hlast, hne, hi]

theorem modelStage_active_update {n k : ℕ} (hk : k < n) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    modelStage n (k + 1) i j =
      modelStage n k i j + modelStage n k ⟨k, hk⟩ j / 2 := by
  have hi' : k + 1 ≤ i.val := hi
  have hj' : k + 1 ≤ j.val := hj
  have hne : (⟨k, hk⟩ : Fin n) ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  have hnlt : ¬j < (⟨k, hk⟩ : Fin n) := by
    exact not_lt_of_ge hj.le
  by_cases hlast : j.val + 1 = n
  · simp [modelStage, hi', hj', hi.le, hj.le, hlast, pow_succ]
    ring
  · simp [modelStage, hi', hj', hi.le, hj.le, hlast, hne, hnlt]

theorem modelStage_schur {n k : ℕ} (hk : k < n) :
    schurStep (modelStage n k) ⟨k, hk⟩ ⟨k, hk⟩ = modelStage n (k + 1) := by
  ext i j
  simp only [schurStep, rowSwap, Equiv.swap_self, Equiv.refl_apply]
  by_cases hij : (⟨k, hk⟩ : Fin n) < i ∧ (⟨k, hk⟩ : Fin n) < j
  · rw [if_pos hij]
    have hk' : k + 1 < n := lt_of_le_of_lt hij.1 i.isLt
    have hlast : k + 1 ≠ n := by omega
    rw [modelStage_pivot hk, if_neg hlast, modelStage_lower_pivot hk hk' i hij.1,
      modelStage_active_update hk i j hij.1 hij.2]
    ring
  · have hnot : ¬(k + 1 ≤ i.val ∧ k + 1 ≤ j.val) := hij
    simp only [if_neg hij, modelStage, if_neg hnot]

theorem witness_trajectory {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk : k < n) :
    trajectory (witnessMatrix n) (noSwapPath n) k = modelStage n k := by
  induction k with
  | zero => simpa only [trajectory] using (modelStage_zero n).symm
  | succ k ih =>
      have hkn : k < n := by omega
      simpa only [trajectory, dif_pos hkn, noSwapPath, ih hkn] using modelStage_schur hkn

theorem modelStage_abs_bound (n k : ℕ) (i j : Fin n) :
    |modelStage n k i j| ≤ (3 / 2 : ℝ) ^ k := by
  have hp : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hp0 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ k := by positivity
  unfold modelStage
  split_ifs <;> norm_num [abs_of_nonneg hp0] <;> linarith

theorem witness_strict {n : ℕ} (hn : 2 ≤ n) : StrictNoSwapPath (witnessMatrix n) := by
  intro k
  rw [witness_trajectory hn k.val k.isLt]
  have hp := modelStage_pivot k.isLt
  by_cases hlast : k.val + 1 = n
  · rw [if_pos hlast] at hp
    refine ⟨by rw [hp]; positivity, ?_⟩
    intro i hi
    have hin := i.isLt
    have hki : k.val < i.val := hi
    omega
  · rw [if_neg hlast] at hp
    refine ⟨by rw [hp]; norm_num, ?_⟩
    intro i hi
    rw [hp, modelStage_lower_pivot k.isLt (by omega) i hi]
    norm_num

theorem witness_entryMax {n : ℕ} (hn : 2 ≤ n) : entryMax (witnessMatrix n) = 1 := by
  apply le_antisymm
  · rw [← activeMax_zero_proved]
    apply activeMax_le_proved _ _ _ (by norm_num)
    intro i j hi hj
    simpa only [modelStage_zero, pow_zero] using modelStage_abs_bound n 0 i j
  · let last : Fin n := ⟨n - 1, by omega⟩
    have hlast : last.val + 1 = n := by dsimp [last]; omega
    have h := abs_le_entryMax_proved (witnessMatrix n) last last
    simpa only [witnessMatrix, hlast, if_true, abs_one] using h

theorem witness_peakMax {n : ℕ} (hn : 2 ≤ n) :
    peakMax (witnessMatrix n) (noSwapPath n) = (3 / 2 : ℝ) ^ (n - 1) := by
  apply le_antisymm
  · apply peakMax_le_proved _ _ _ (by positivity)
    intro k
    rw [witness_trajectory hn k.val k.isLt]
    apply activeMax_le_proved _ _ _ (by positivity)
    intro i j hi hj
    exact (modelStage_abs_bound n k.val i j).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  · let last : Fin n := ⟨n - 1, by omega⟩
    have hlast : last.val + 1 = n := by dsimp [last]; omega
    have hentry := abs_le_activeMax_proved
      (trajectory (witnessMatrix n) (noSwapPath n) last.val) last.val last last le_rfl le_rfl
    rw [witness_trajectory hn last.val last.isLt, modelStage_pivot last.isLt,
      if_pos hlast, abs_of_nonneg (by positivity)] at hentry
    exact hentry.trans (activeMax_le_peakMax_proved (witnessMatrix n) (noSwapPath n) last)

theorem witness_strict_growth {n : ℕ} (hn : 2 ≤ n) :
    (witnessMatrix n).det ≠ 0 ∧ StrictNoSwapPath (witnessMatrix n) ∧
      AdmissiblePath (witnessMatrix n) (noSwapPath n) ∧
      growth (witnessMatrix n) (noSwapPath n) = (3 / 2 : ℝ) ^ (n - 1) := by
  have hs := witness_strict hn
  refine ⟨noSwap_nonsingular_of_pivots _ (fun k => (hs k).1.ne'), hs,
    strictNoSwap_admissible _ hs, ?_⟩
  change peakMax (witnessMatrix n) (noSwapPath n) / entryMax (witnessMatrix n) = _
  rw [witness_entryMax hn, witness_peakMax hn, div_one]

#assert_trust kernel witness_trajectory
#print axioms witness_trajectory
#assert_trust kernel witness_strict_growth
#print axioms witness_strict_growth

end NLA.IE04
