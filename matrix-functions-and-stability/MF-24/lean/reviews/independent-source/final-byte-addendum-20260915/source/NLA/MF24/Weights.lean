/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Geometry
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open scoped BigOperators

lemma sum_le_one_exception {α : Type*} (s : Finset α) (bad : α → Prop)
    [DecidablePred bad] (f : α → ℝ) (m : ℕ) (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi) (hcard : s.card ≤ m + 1)
    (hbad : (s.filter bad).card ≤ 1)
    (hf : ∀ v ∈ s, f v ≤ if bad v then hi else lo) :
    ∑ v ∈ s, f v ≤ hi + (m : ℝ) * lo := by
  have hpoint : ∀ v ∈ s, f v ≤ lo + if bad v then hi - lo else 0 := by
    intro v hv
    specialize hf v hv
    split_ifs at hf ⊢ <;> linarith
  have hsum := Finset.sum_le_sum hpoint
  have hconst : (∑ v ∈ s, if bad v then hi - lo else 0) =
      ((s.filter bad).card : ℝ) * (hi - lo) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, hconst] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hcard
  have hb : ((s.filter bad).card : ℝ) ≤ 1 := by exact_mod_cast hbad
  have hbase := mul_le_mul_of_nonneg_right hc hlo
  have hexc := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hhi)
  nlinarith

lemma inverse_weight_point_bound (m : ℕ) (t : ℝ) (ht : 1 < t)
    (v : Fin (dimension m)) :
    inverseHeightWeight m t v ^ 2 ≤
      if heightY m v.val = 0 then 1 else 1 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have ha0 : 0 ≤ 1 / t ^ 2 := by positivity
  have ha1 : 1 / t ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos ht0)).mpr ht2
  have hh := (height_bounds m v.val).2
  by_cases h0 : heightY m v.val = 0
  · simp [inverseHeightWeight, heightWeight, h0]
  · rw [if_neg h0]
    by_cases h1 : heightY m v.val = 1
    · simp [inverseHeightWeight, heightWeight, h1, one_div, inv_pow]
    · have h2 : heightY m v.val = 2 := by omega
      have haa : (1 / t ^ 2) ^ 2 ≤ 1 / t ^ 2 := by nlinarith
      simpa only [inverseHeightWeight, heightWeight, h2, one_div] using haa

lemma weight_point_bound (m : ℕ) (t : ℝ) (ht : 1 < t)
    (v : Fin (dimension m)) :
    heightWeight m t v ^ 2 ≤
      if heightY m v.val = 2 then t ^ 4 else t ^ 2 := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hh := (height_bounds m v.val).2
  by_cases h2 : heightY m v.val = 2
  · simp [heightWeight, h2, ← pow_mul]
  · rw [if_neg h2]
    by_cases h1 : heightY m v.val = 1
    · simp [heightWeight, h1]
    · have h0 : heightY m v.val = 0 := by omega
      simpa [heightWeight, h0] using ht2

theorem residue_weight_bounds (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) (c : Fin (stride m)) :
    (∑ v ∈ residueClass m c, inverseHeightWeight m t v ^ 2) ≤
      1 + (m : ℝ) / t ^ 2 ∧
    (∑ v ∈ residueClass m c, heightWeight m t v ^ 2) ≤
      t ^ 4 + (m : ℝ) * t ^ 2 := by
  have hg := (residue_geometry m hm).2 c
  have ht0 : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  constructor
  · have hlo : 0 ≤ 1 / t ^ 2 := by positivity
    have hhi : 1 / t ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos ht0)).mpr ht2
    have he := sum_le_one_exception (residueClass m c) (fun v => heightY m v.val = 0)
      (fun v => inverseHeightWeight m t v ^ 2) m (1 / t ^ 2) 1
      hlo hhi hg.1 hg.2.1 (fun v _ => inverse_weight_point_bound m t ht v)
    simpa [div_eq_mul_inv] using he
  · have hlo : 0 ≤ t ^ 2 := sq_nonneg t
    have hhi : t ^ 2 ≤ t ^ 4 := by nlinarith [sq_nonneg (t ^ 2 - 1)]
    exact sum_le_one_exception (residueClass m c) (fun v => heightY m v.val = 2)
      (fun v => heightWeight m t v ^ 2) m (t ^ 2) (t ^ 4)
      hlo hhi hg.1 hg.2.2 (fun v _ => weight_point_bound m t ht v)

#assert_trust kernel residue_weight_bounds
#print axioms residue_weight_bounds

end NLA.MF24
