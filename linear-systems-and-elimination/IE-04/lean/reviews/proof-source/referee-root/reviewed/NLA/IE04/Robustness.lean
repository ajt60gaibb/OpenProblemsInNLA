/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

A symbolic induction covers the entire closed perturbation box, every
dimension and every admissible tie rule. The determinant and trajectory
bridges are explicit; no robustness certificate is assumed.
-/
import NLA.IE04.Witness
import NLA.IE04.Scalars
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal
noncomputable section
namespace NLA.IE04

theorem noSwap_box_stage_bound {n : ℕ} (hn : 2 ≤ n) (A : Mat n)
    (hbox : InWitnessBox A) (k : ℕ) (hk : k < n) :
    activeMax (trajectory A (noSwapPath n) k - modelStage n k) k ≤
      stageAmplification n ^ k * boxRadius n := by
  induction k with
  | zero =>
      simp only [trajectory, modelStage_zero, pow_zero, one_mul]
      apply activeMax_le_proved _ _ _ (scalar_budgets hn).1.le
      intro i j hi hj
      exact hbox i j
  | succ k ih =>
      have hkn : k < n := by omega
      have hbudget := (scalar_budgets hn).2.2.2 k hkn
      let e : ℝ := stageAmplification n ^ k * boxRadius n
      have he : 0 ≤ e := by dsimp [e, stageAmplification, boxRadius]; positivity
      have he' : e ≤ 1 / 8 := hbudget.1
      have hentries : ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
          |trajectory A (noSwapPath n) k i j - modelStage n k i j| ≤ e := by
        intro i j hi hj
        exact (abs_le_activeMax_proved
          (trajectory A (noSwapPath n) k - modelStage n k) k i j hi hj).trans (ih hkn)
      apply activeMax_le_proved _ _ _ (by unfold stageAmplification boxRadius; positivity)
      intro i j hi hj
      have hki : (⟨k, hkn⟩ : Fin n) < i := hi
      have hkj : (⟨k, hkn⟩ : Fin n) < j := hj
      have hlast : k + 1 ≠ n := by omega
      have hp := hentries ⟨k, hkn⟩ ⟨k, hkn⟩ le_rfl le_rfl
      rw [modelStage_pivot hkn, if_neg hlast] at hp
      have ha := hentries i ⟨k, hkn⟩ hki.le le_rfl
      rw [modelStage_lower_pivot hkn hk i hki] at ha
      have ha' : |trajectory A (noSwapPath n) k i ⟨k, hkn⟩ + 1 / 2| ≤ e := by
        simpa only [sub_neg_eq_add] using ha
      have hv0 : |modelStage n k ⟨k, hkn⟩ j| ≤ (2 : ℝ) ^ n :=
        (modelStage_abs_bound n k ⟨k, hkn⟩ j).trans hbudget.2.2
      have hs := scalar_schur_error n e
        (trajectory A (noSwapPath n) k ⟨k, hkn⟩ ⟨k, hkn⟩)
        (trajectory A (noSwapPath n) k i ⟨k, hkn⟩)
        (trajectory A (noSwapPath n) k i j) (modelStage n k i j)
        (trajectory A (noSwapPath n) k ⟨k, hkn⟩ j) (modelStage n k ⟨k, hkn⟩ j)
        he he' hp ha' (hentries i j hki.le hkj.le)
        (hentries ⟨k, hkn⟩ j le_rfl hkj.le) hv0
      simp only [Matrix.sub_apply, trajectory, dif_pos hkn, noSwapPath, schurStep,
        rowSwap, Equiv.swap_self, Equiv.refl_apply, hki, hkj, and_self, if_true]
      rw [modelStage_active_update hkn i j hki hkj]
      calc
        _ ≤ stageAmplification n * e := hs
        _ = stageAmplification n ^ (k + 1) * boxRadius n := by
          dsimp [e]
          rw [pow_succ]
          ring

theorem noSwap_box_entry_error {n : ℕ} (hn : 2 ≤ n) (A : Mat n)
    (hbox : InWitnessBox A) (k : ℕ) (hk : k < n) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) :
    |trajectory A (noSwapPath n) k i j - modelStage n k i j| ≤
      stageAmplification n ^ k * boxRadius n :=
  (abs_le_activeMax_proved (trajectory A (noSwapPath n) k - modelStage n k)
    k i j hi hj).trans (noSwap_box_stage_bound hn A hbox k hk)

theorem strictNoSwap_on_box {n : ℕ} (hn : 2 ≤ n) (A : Mat n)
    (hbox : InWitnessBox A) : StrictNoSwapPath A := by
  intro k
  let e : ℝ := stageAmplification n ^ k.val * boxRadius n
  have he : 0 ≤ e := by dsimp [e, stageAmplification, boxRadius]; positivity
  have hbudget := (scalar_budgets hn).2.2.2 k.val k.isLt
  have he' : e ≤ 1 / 8 := hbudget.1
  have hdiag := noSwap_box_entry_error hn A hbox k.val k.isLt k k le_rfl le_rfl
  have hmodel : (1 : ℝ) ≤ modelStage n k.val k k := by
    rw [modelStage_pivot k.isLt]
    split_ifs
    · exact hbudget.2.1
    · exact le_rfl
  have hpbound : 7 / 8 ≤ trajectory A (noSwapPath n) k.val k k := by
    have hd := (abs_le.mp hdiag).1
    change -e ≤ _ at hd
    linarith
  refine ⟨by linarith, ?_⟩
  intro i hi
  have hk' : k.val + 1 < n := lt_of_le_of_lt hi i.isLt
  have hlast : k.val + 1 ≠ n := by omega
  have hp := noSwap_box_entry_error hn A hbox k.val k.isLt k k le_rfl le_rfl
  rw [modelStage_pivot k.isLt, if_neg hlast] at hp
  have ha := noSwap_box_entry_error hn A hbox k.val k.isLt i k hi.le le_rfl
  rw [modelStage_lower_pivot k.isLt hk' i hi] at ha
  have ha' : |trajectory A (noSwapPath n) k.val i k + 1 / 2| ≤ e := by
    simpa only [sub_neg_eq_add] using ha
  have hab := (quotient_bounds e _ _ he he' hp ha').2.1
  linarith

theorem full_box_robust {n : ℕ} (hn : 2 ≤ n) (A : Mat n)
    (hbox : InWitnessBox A) :
    A.det ≠ 0 ∧ StrictNoSwapPath A ∧ AdmissiblePath A (noSwapPath n) ∧
      (∀ path, AdmissiblePath A path → path = noSwapPath n) ∧
      ∀ k : ℕ, k < n →
        activeMax (trajectory A (noSwapPath n) k - modelStage n k) k ≤
          stageAmplification n ^ k * boxRadius n := by
  have hs := strictNoSwap_on_box hn A hbox
  exact ⟨noSwap_nonsingular_of_pivots A (fun k => (hs k).1.ne'), hs,
    strictNoSwap_admissible A hs, fun path hp => strictNoSwap_path_unique A hs path hp,
    noSwap_box_stage_bound hn A hbox⟩

theorem entryMax_on_box {n : ℕ} (hn : 2 ≤ n) (A : Mat n) (hbox : InWitnessBox A) :
    entryMax A ≤ 9 / 8 := by
  obtain ⟨i, j, hij⟩ := (entryMax_semantics_proved (by omega : 1 ≤ n) A).2.2
  rw [hij]
  have hδ := (scalar_budgets hn).2.1
  have hw : |witnessMatrix n i j| ≤ 1 := by
    simpa only [modelStage_zero, pow_zero] using modelStage_abs_bound n 0 i j
  calc
    |A i j| = |(A i j - witnessMatrix n i j) + witnessMatrix n i j| := by
      congr 1
      ring
    _ ≤ |A i j - witnessMatrix n i j| + |witnessMatrix n i j| := abs_add_le _ _
    _ ≤ boxRadius n + 1 := add_le_add (hbox i j) hw
    _ ≤ 9 / 8 := by linarith

theorem growth_on_box {n : ℕ} (hn : 2 ≤ n) (A : Mat n)
    (hbox : InWitnessBox A) (path : PivotPath n) (hpath : AdmissiblePath A path) :
    0 < entryMax A ∧ entryMax A ≤ 9 / 8 ∧
      growthThreshold n < growth A path := by
  have hE := (gepp_growth_bound_proved (by omega : 1 ≤ n) A path hpath).1
  have hEupper := entryMax_on_box hn A hbox
  obtain ⟨hdet, hs, ha, hunique, hstages⟩ := full_box_robust hn A hbox
  have hpath_eq := hunique path hpath
  subst path
  refine ⟨hE, hEupper, ?_⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : last.val + 1 = n := by dsimp [last]; omega
  have hr : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ (n - 1) := one_le_pow₀ (by norm_num)
  have herr := noSwap_box_entry_error hn A hbox last.val last.isLt last last le_rfl le_rfl
  have he := (scalar_budgets hn).2.2.2 last.val last.isLt
  rw [modelStage_pivot last.isLt, if_pos hlast] at herr
  have hdiag : (3 / 2 : ℝ) ^ (n - 1) - 1 / 8 ≤
      trajectory A (noSwapPath n) last.val last last := by
    have hl := (abs_le.mp herr).1
    change -(stageAmplification n ^ (n - 1) * boxRadius n) ≤
      trajectory A (noSwapPath n) last.val last last - (3 / 2 : ℝ) ^ (n - 1) at hl
    have hsmall := he.1
    change stageAmplification n ^ (n - 1) * boxRadius n ≤ 1 / 8 at hsmall
    linarith
  have hpeak : (3 / 2 : ℝ) ^ (n - 1) - 1 / 8 ≤ peakMax A (noSwapPath n) :=
    hdiag.trans ((le_abs_self _).trans
      ((abs_le_activeMax_proved (trajectory A (noSwapPath n) last.val)
        last.val last last le_rfl le_rfl).trans
        (activeMax_le_peakMax_proved A (noSwapPath n) last)))
  change (3 / 2 : ℝ) ^ (n - 1) / 2 < peakMax A (noSwapPath n) / entryMax A
  apply (lt_div_iff₀ hE).mpr
  have hprod := mul_le_mul_of_nonneg_left hEupper
    (show (0 : ℝ) ≤ (3 / 2 : ℝ) ^ (n - 1) / 2 by positivity)
  nlinarith

#assert_trust kernel full_box_robust
#print axioms full_box_robust
#assert_trust kernel growth_on_box
#print axioms growth_on_box

end NLA.IE04
