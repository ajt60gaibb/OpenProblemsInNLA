/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

All vertices are retained. Cardinality bounds use injections and congruence
cancellation, never enumeration of the growing finite matrices.
-/
import NLA.MF24.Heights
import NLA.MF24.Polynomial
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

@[simp] lemma mem_residueClass (m : ℕ) (c : Fin (stride m))
    (v : Fin (dimension m)) :
    v ∈ residueClass m c ↔ v.val % stride m = c.val := by simp [residueClass]

lemma vertex_residue_quotient (m : ℕ) (v : Fin (dimension m)) :
    v.val / stride m < m + 1 := by
  apply (Nat.div_lt_iff_lt_mul (stride_pos m)).mpr
  have hv : v.val < m * stride m + 1 := by
    calc v.val < dimension m := v.isLt
      _ = m * stride m + 1 := dimension_eq m
  have hd := stride_pos m
  nlinarith

lemma residue_card_bound (m : ℕ) (c : Fin (stride m)) :
    (residueClass m c).card ≤ m + 1 := by
  calc
    (residueClass m c).card ≤ (Finset.range (m + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun v : Fin (dimension m) => v.val / stride m)
      · intro v _
        exact Finset.mem_range.mpr (vertex_residue_quotient m v)
      · intro v hv w hw he
        change v.val / stride m = w.val / stride m at he
        have hvmod := (mem_residueClass m c v).mp hv
        have hwmod := (mem_residueClass m c w).mp hw
        have hdv := Nat.div_add_mod' v.val (stride m)
        have hdw := Nat.div_add_mod' w.val (stride m)
        rw [he, hvmod] at hdv
        rw [hwmod] at hdw
        exact Fin.ext (hdv.symm.trans hdw)
    _ = m + 1 := Finset.card_range _

lemma heightY_zero_iff (m : ℕ) (v : Fin (dimension m)) :
    heightY m v.val = 0 ↔
      v.val % (m + 1) = 0 ∧ v.val / (m + 1) < m := by
  have hbound : v.val / (m + 1) ≤ m := (vertex_grid_bounds m v.val v.isLt).1
  constructor
  · intro hz
    change (if 1 ≤ v.val % (m + 1) then (1 : ℕ) else 0) +
      (if v.val / (m + 1) = m then (1 : ℕ) else 0) = 0 at hz
    obtain ⟨hfirst, hsecond⟩ := Nat.add_eq_zero_iff.mp hz
    have hrem : v.val % (m + 1) = 0 := by
      by_contra hr
      have hpos : 1 ≤ v.val % (m + 1) := Nat.one_le_iff_ne_zero.mpr hr
      exact Nat.one_ne_zero ((if_pos hpos).symm.trans hfirst)
    have hquot : v.val / (m + 1) ≠ m := by
      intro he
      exact Nat.one_ne_zero ((if_pos he).symm.trans hsecond)
    exact ⟨hrem, Nat.lt_of_le_of_ne hbound hquot⟩
  · rintro ⟨hrem, hquot⟩
    simp [heightY, hrem, Nat.ne_of_lt hquot]

lemma heightY_two_iff (m v : ℕ) :
    heightY m v = 2 ↔ 1 ≤ v % (m + 1) ∧ v / (m + 1) = m := by
  unfold heightY
  split_ifs <;> omega

lemma stride_coprime (m : ℕ) : Nat.gcd (stride m) (m + 1) = 1 := by
  change Nat.Coprime ((m + 1) + 1) (m + 1)
  simp

lemma zero_height_same_residue (m : ℕ) (c : Fin (stride m))
    (v w : Fin (dimension m))
    (hv : v ∈ residueClass m c) (hw : w ∈ residueClass m c)
    (hv0 : heightY m v.val = 0) (hw0 : heightY m w.val = 0) : v = w := by
  have hzv := (heightY_zero_iff m v).mp hv0
  have hzw := (heightY_zero_iff m w).mp hw0
  have hvform : v.val = (v.val / (m + 1)) * (m + 1) := by
    have he := Nat.div_add_mod' v.val (m + 1)
    rw [hzv.1, Nat.add_zero] at he
    exact he.symm
  have hwform : w.val = (w.val / (m + 1)) * (m + 1) := by
    have he := Nat.div_add_mod' w.val (m + 1)
    rw [hzw.1, Nat.add_zero] at he
    exact he.symm
  have hcon : Nat.ModEq (stride m) v.val w.val :=
    ((mem_residueClass m c v).mp hv).trans ((mem_residueClass m c w).mp hw).symm
  rw [hvform, hwform] at hcon
  have hquot := Nat.ModEq.cancel_right_of_coprime (stride_coprime m) hcon
  have he : v.val / (m + 1) = w.val / (m + 1) :=
    hquot.eq_of_lt_of_lt (by unfold stride; omega) (by unfold stride; omega)
  apply Fin.ext
  calc v.val = (v.val / (m + 1)) * (m + 1) := hvform
    _ = (w.val / (m + 1)) * (m + 1) := by rw [he]
    _ = w.val := hwform.symm

lemma two_height_same_residue (m : ℕ) (c : Fin (stride m))
    (v w : Fin (dimension m))
    (hv : v ∈ residueClass m c) (hw : w ∈ residueClass m c)
    (hv2 : heightY m v.val = 2) (hw2 : heightY m w.val = 2) : v = w := by
  have hzv := (heightY_two_iff m v.val).mp hv2
  have hzw := (heightY_two_iff m w.val).mp hw2
  have hvform : v.val = m * (m + 1) + v.val % (m + 1) := by
    have he := Nat.div_add_mod' v.val (m + 1)
    rw [hzv.2] at he
    exact he.symm
  have hwform : w.val = m * (m + 1) + w.val % (m + 1) := by
    have he := Nat.div_add_mod' w.val (m + 1)
    rw [hzw.2] at he
    exact he.symm
  have hcon : Nat.ModEq (stride m) v.val w.val :=
    ((mem_residueClass m c v).mp hv).trans ((mem_residueClass m c w).mp hw).symm
  rw [hvform, hwform] at hcon
  have hrem := Nat.ModEq.add_left_cancel' (m * (m + 1)) hcon
  have he : v.val % (m + 1) = w.val % (m + 1) :=
    hrem.eq_of_lt_of_lt
      (by have := Nat.mod_lt v.val (show 0 < m + 1 by omega); unfold stride; omega)
      (by have := Nat.mod_lt w.val (show 0 < m + 1 by omega); unfold stride; omega)
  apply Fin.ext
  calc v.val = m * (m + 1) + v.val % (m + 1) := hvform
    _ = m * (m + 1) + w.val % (m + 1) := by rw [he]
    _ = w.val := hwform.symm

theorem residue_geometry (m : ℕ) (hm : 2 ≤ m) :
    (∀ v : Fin (dimension m), ∃! c : Fin (stride m), v ∈ residueClass m c) ∧
    ∀ c : Fin (stride m),
      (residueClass m c).card ≤ m + 1 ∧
      ((residueClass m c).filter (fun v => heightY m v.val = 0)).card ≤ 1 ∧
      ((residueClass m c).filter (fun v => heightY m v.val = 2)).card ≤ 1 := by
  constructor
  · intro v
    refine ⟨⟨v.val % stride m, Nat.mod_lt _ (stride_pos m)⟩, ?_, ?_⟩
    · exact (mem_residueClass _ _ _).mpr rfl
    · intro c hc
      exact Fin.ext ((mem_residueClass m c v).mp hc).symm
  · intro c
    refine ⟨residue_card_bound m c, ?_, ?_⟩
    · apply Finset.card_le_one.mpr
      intro v hv w hw
      obtain ⟨hv, hv0⟩ := Finset.mem_filter.mp hv
      obtain ⟨hw, hw0⟩ := Finset.mem_filter.mp hw
      exact zero_height_same_residue m c v w hv hw hv0 hw0
    · apply Finset.card_le_one.mpr
      intro v hv w hw
      obtain ⟨hv, hv2⟩ := Finset.mem_filter.mp hv
      obtain ⟨hw, hw2⟩ := Finset.mem_filter.mp hw
      exact two_height_same_residue m c v w hv hw hv2 hw2

#assert_trust kernel residue_geometry
#print axioms residue_geometry

end NLA.MF24
