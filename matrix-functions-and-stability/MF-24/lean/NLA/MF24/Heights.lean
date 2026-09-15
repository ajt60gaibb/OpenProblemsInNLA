/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

This module proves the source-list/height identity. Height coordinates do not
replace the original matrices by a separately defined counterexample.
-/
import NLA.MF24.Words
import NLA.MF24.Powers
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

lemma grid_div_mod (m q s : ℕ) (hs : s < m + 1) :
    (q * (m + 1) + s) / (m + 1) = q ∧
    (q * (m + 1) + s) % (m + 1) = s := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt hs, Nat.zero_add]
  · exact Nat.mul_add_mod_of_lt hs

lemma heightX_grid (m q s : ℕ) (hs : s < m + 1) :
    heightX m (q * (m + 1) + s) =
      (if 1 ≤ s then 1 else 0) + (if 1 ≤ q then 1 else 0) := by
  simp only [heightX, (grid_div_mod m q s hs).1, (grid_div_mod m q s hs).2]

lemma heightY_grid (m q s : ℕ) (hs : s < m + 1) :
    heightY m (q * (m + 1) + s) =
      (if 1 ≤ s then 1 else 0) + (if q = m then 1 else 0) := by
  simp only [heightY, (grid_div_mod m q s hs).1, (grid_div_mod m q s hs).2]

lemma height_bounds (m v : ℕ) : heightX m v ≤ 2 ∧ heightY m v ≤ 2 := by
  unfold heightX heightY
  split_ifs <;> omega

lemma motif_height_ratio (s d : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ ((if 1 ≤ s + 1 then 1 else 0) + d) /
      t ^ ((if 1 ≤ s then 1 else 0) + d) = (if s = 0 then t else 1) := by
  by_cases hs : s = 0
  · subst s
    simp [pow_add, ne_of_gt ht]
  · have hs1 : 1 ≤ s := by omega
    have hs2 : 1 ≤ s + 1 := by omega
    simp [hs, hs1, hs2, pow_ne_zero _ (ne_of_gt ht)]

lemma motif_height_ratios (m q s : ℕ) (hs : s < m) (t : ℝ) (ht : 0 < t) :
    t ^ heightX m (q * (m + 1) + s + 1) /
      t ^ heightX m (q * (m + 1) + s) = (if s = 0 then t else 1) ∧
    t ^ heightY m (q * (m + 1) + s + 1) /
      t ^ heightY m (q * (m + 1) + s) = (if s = 0 then t else 1) := by
  have hnext : q * (m + 1) + s + 1 = q * (m + 1) + (s + 1) := by omega
  rw [hnext]
  constructor
  · rw [heightX_grid m q (s + 1) (by omega), heightX_grid m q s (by omega)]
    exact motif_height_ratio s _ t ht
  · rw [heightY_grid m q (s + 1) (by omega), heightY_grid m q s (by omega)]
    exact motif_height_ratio s _ t ht

lemma bridge_height_ratios (m : ℕ) (hm : 2 ≤ m) (q : ℕ) (hq : q < m)
    (t : ℝ) (ht : 0 < t) :
    t ^ heightX m (q * (m + 1) + m + 1) /
      t ^ heightX m (q * (m + 1) + m) = (if q = 0 then 1 else t⁻¹) ∧
    t ^ heightY m (q * (m + 1) + m + 1) /
      t ^ heightY m (q * (m + 1) + m) = (if q + 1 = m then 1 else t⁻¹) := by
  have hnext : q * (m + 1) + m + 1 = (q + 1) * (m + 1) + 0 := by ring
  have hm1 : 1 ≤ m := by omega
  rw [hnext]
  constructor
  · rw [heightX_grid m (q + 1) 0 (by omega), heightX_grid m q m (by omega)]
    by_cases hq0 : q = 0
    · subst q
      simp [hm1, ne_of_gt ht]
    · have hq1 : 1 ≤ q := by omega
      have hq2 : 1 ≤ q + 1 := by omega
      simp only [show ¬ (1 : ℕ) ≤ 0 by omega, hq1, hq2, hm1, hq0,
        if_false, if_true, Nat.zero_add, one_add_one_eq_two, pow_one]
      field_simp [ne_of_gt ht] <;> ring
  · rw [heightY_grid m (q + 1) 0 (by omega), heightY_grid m q m (by omega)]
    have hqm : q ≠ m := by omega
    by_cases hlast : q + 1 = m <;> simp [hm1, hqm, hlast, ne_of_gt ht]

lemma vertex_grid_bounds (m v : ℕ) (hv : v < dimension m) :
    v / (m + 1) ≤ m ∧ v % (m + 1) ≤ m := by
  have hmod := Nat.mod_lt v (show 0 < m + 1 by omega)
  have hdecomp := Nat.div_add_mod' v (m + 1)
  constructor
  · by_contra hn
    have hlarge : m + 1 ≤ v / (m + 1) := by omega
    have hmul := Nat.mul_le_mul_right (m + 1) hlarge
    have hbound : (m + 1) * (m + 1) ≤ v := by omega
    have hv' : v < (m + 1) * (m + 1) := by
      simpa only [dimension, pow_two] using hv
    omega
  · omega

lemma source_edge_height_ratios (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : 0 < t)
    (v : ℕ) (hv : v + 1 < dimension m) :
    (sourceWordX m t).getD v 0 = t ^ heightX m (v + 1) / t ^ heightX m v ∧
    (sourceWordY m t).getD v 0 = t ^ heightY m (v + 1) / t ^ heightY m v := by
  let q := v / (m + 1)
  let s := v % (m + 1)
  have hdecomp : q * (m + 1) + s = v := Nat.div_add_mod' v (m + 1)
  have hbounds := vertex_grid_bounds m v (by omega)
  have hq : q ≤ m := hbounds.1
  have hs : s ≤ m := hbounds.2
  by_cases hsm : s < m
  · have hw := source_motif_getD m hm t q s hq hsm
    have hh := motif_height_ratios m q s hsm t ht
    rw [hdecomp] at hw hh
    exact ⟨hw.1.trans hh.1.symm, hw.2.trans hh.2.symm⟩
  · have hseq : s = m := by omega
    have hqlt : q < m := by
      by_contra hn
      have hqeq : q = m := by omega
      unfold dimension at hv
      rw [hqeq, hseq] at hdecomp
      nlinarith
    have hw := source_bridge_getD m hm t q hqlt
    have hh := bridge_height_ratios m hm q hqlt t ht
    have hd : q * (m + 1) + m = v := by simpa [hseq] using hdecomp
    rw [hd] at hw hh
    exact ⟨hw.1.trans hh.1.symm, hw.2.trans hh.2.symm⟩

theorem source_words_eq_height_shifts (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    matrixX m t = heightShift (fun v => heightX m v.val) t ∧
    matrixY m t = heightShift (fun v => heightY m v.val) t ∧
    heightX m 0 = 0 ∧ heightY m 0 = 0 ∧
    ∀ v : Fin (dimension m), heightX m v.val ≤ 2 ∧ heightY m v.val ≤ 2 := by
  have ht0 : 0 < t := by linarith
  refine ⟨?_, ?_, ?_, ?_, fun v => height_bounds m v.val⟩
  · ext r s
    simp only [matrixX, wordShift, heightShift]
    split_ifs with he
    · rw [(source_edge_height_ratios m hm t ht0 r.val (by rw [he]; exact s.isLt)).1,
        he]
    · rfl
  · ext r s
    simp only [matrixY, wordShift, heightShift]
    split_ifs with he
    · rw [(source_edge_height_ratios m hm t ht0 r.val (by rw [he]; exact s.isLt)).2,
        he]
    · rfl
  · simp [heightX]
  · have h0m : 0 ≠ m := by omega
    simp [heightY, h0m]

theorem family_nilpotent_nonnegative (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    matrixX m t ^ dimension m = 0 ∧ matrixY m t ^ dimension m = 0 ∧
    ∀ r s : Fin (dimension m),
      (matrixX m t r s).im = 0 ∧ 0 ≤ (matrixX m t r s).re ∧
      (matrixY m t r s).im = 0 ∧ 0 ≤ (matrixY m t r s).re := by
  have hh := source_words_eq_height_shifts m hm t ht
  have ht0 : 0 < t := by linarith
  rw [hh.1, hh.2.1]
  refine ⟨height_shift_nilpotent _ _ t ht0, height_shift_nilpotent _ _ t ht0, ?_⟩
  intro r s
  have hx := height_shift_real_nonnegative (dimension m) (fun v => heightX m v.val) t ht0 r s
  have hy := height_shift_real_nonnegative (dimension m) (fun v => heightY m v.val) t ht0 r s
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

#assert_trust kernel source_words_eq_height_shifts
#assert_trust kernel family_nilpotent_nonnegative
#print axioms source_words_eq_height_shifts
#print axioms family_nilpotent_nonnegative

end NLA.MF24
