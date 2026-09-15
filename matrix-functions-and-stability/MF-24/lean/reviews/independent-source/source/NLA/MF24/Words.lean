/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

Source words are indexed by motif number and position. The proofs recurse on
the bridge list, so no dimension-dependent list is enumerated by evaluation.
-/
import NLA.MF24.Dimensions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

def weave {α : Type*} (l bridges : List α) : List α :=
  l ++ (bridges.map (fun b => b :: l)).flatten

lemma weave_nil {α : Type*} (l : List α) : weave l [] = l := by simp [weave]

lemma weave_cons {α : Type*} (l : List α) (b : α) (bs : List α) :
    weave l (b :: bs) = (l ++ [b]) ++ weave l bs := by
  simp [weave, List.append_assoc]

lemma weave_motif_getD {α : Type*} (l bs : List α) (d : α)
    (q s : ℕ) (hq : q ≤ bs.length) (hs : s < l.length) :
    (weave l bs).getD (q * (l.length + 1) + s) d = l.getD s d := by
  induction bs generalizing q with
  | nil =>
      have hq0 : q = 0 := by simpa using hq
      simp [hq0, weave_nil]
  | cons b bs ih =>
      rw [weave_cons]
      cases q with
      | zero =>
          simp only [zero_mul, zero_add]
          rw [List.getD_append _ _ d s (by simp; omega)]
          exact List.getD_append _ _ d s hs
      | succ q =>
          have hlen : (l ++ [b]).length = l.length + 1 := by simp
          rw [List.getD_append_right _ _ d _ (by rw [hlen]; nlinarith)]
          rw [hlen]
          have hind : (q + 1) * (l.length + 1) + s - (l.length + 1) =
              q * (l.length + 1) + s := by
            rw [Nat.add_mul]
            omega
          rw [hind]
          exact ih q (by simpa using hq)

lemma weave_bridge_getD {α : Type*} (l bs : List α) (d : α)
    (q : ℕ) (hq : q < bs.length) :
    (weave l bs).getD (q * (l.length + 1) + l.length) d = bs.getD q d := by
  induction bs generalizing q with
  | nil => simp at hq
  | cons b bs ih =>
      rw [weave_cons]
      cases q with
      | zero =>
          simp only [zero_mul, zero_add]
          rw [List.getD_append _ _ d _ (by simp)]
          rw [List.getD_append_right _ _ d _ le_rfl]
          simp
      | succ q =>
          have hlen : (l ++ [b]).length = l.length + 1 := by simp
          rw [List.getD_append_right _ _ d _ (by rw [hlen]; nlinarith)]
          rw [hlen]
          have hind : (q + 1) * (l.length + 1) + l.length - (l.length + 1) =
              q * (l.length + 1) + l.length := by
            rw [Nat.add_mul]
            omega
          rw [hind]
          change (weave l bs).getD (q * (l.length + 1) + l.length) d = bs.getD q d
          exact ih q (by simpa using hq)

lemma sourceWordX_weave (m : ℕ) (t : ℝ) :
    sourceWordX m t = weave (motif m t) (1 :: List.replicate (m - 1) t⁻¹) := by
  simp [sourceWordX, weave, inverseBridges, List.map_replicate, List.append_assoc]

lemma sourceWordY_weave (m : ℕ) (t : ℝ) :
    sourceWordY m t = weave (motif m t) (List.replicate (m - 1) t⁻¹ ++ [1]) := by
  simp [sourceWordY, weave, inverseBridges, List.map_replicate, List.append_assoc]

lemma motif_getD (m : ℕ) (t : ℝ) (s : ℕ) (hs : s < m) :
    (motif m t).getD s 0 = if s = 0 then t else 1 := by
  cases s with
  | zero => rfl
  | succ s =>
      change (List.replicate (m - 1) (1 : ℝ)).getD s 0 = 1
      apply List.getD_replicate
      omega

lemma source_motif_getD (m : ℕ) (hm : 2 ≤ m) (t : ℝ)
    (q s : ℕ) (hq : q ≤ m) (hs : s < m) :
    (sourceWordX m t).getD (q * (m + 1) + s) 0 = (if s = 0 then t else 1) ∧
    (sourceWordY m t).getD (q * (m + 1) + s) 0 = (if s = 0 then t else 1) := by
  have hlen := length_motif m (show 1 ≤ m by omega) t
  constructor
  · rw [sourceWordX_weave]
    have he := weave_motif_getD (motif m t) (1 :: List.replicate (m - 1) t⁻¹)
      0 q s (by simp; omega) (by rw [hlen]; exact hs)
    rw [hlen, motif_getD m t s hs] at he
    exact he
  · rw [sourceWordY_weave]
    have he := weave_motif_getD (motif m t) (List.replicate (m - 1) t⁻¹ ++ [1])
      0 q s (by simp; omega) (by rw [hlen]; exact hs)
    rw [hlen, motif_getD m t s hs] at he
    exact he

lemma source_bridge_getD (m : ℕ) (hm : 2 ≤ m) (t : ℝ)
    (q : ℕ) (hq : q < m) :
    (sourceWordX m t).getD (q * (m + 1) + m) 0 =
      (if q = 0 then 1 else t⁻¹) ∧
    (sourceWordY m t).getD (q * (m + 1) + m) 0 =
      (if q + 1 = m then 1 else t⁻¹) := by
  have hlen := length_motif m (show 1 ≤ m by omega) t
  constructor
  · rw [sourceWordX_weave]
    have he := weave_bridge_getD (motif m t) (1 :: List.replicate (m - 1) t⁻¹)
      0 q (by simp; omega)
    rw [hlen] at he
    rw [he]
    cases q with
    | zero => rfl
    | succ q =>
        change (List.replicate (m - 1) t⁻¹).getD q 0 = t⁻¹
        apply List.getD_replicate
        omega
  · rw [sourceWordY_weave]
    have he := weave_bridge_getD (motif m t) (List.replicate (m - 1) t⁻¹ ++ [1])
      0 q (by simp; omega)
    rw [hlen] at he
    rw [he]
    by_cases hlast : q + 1 = m
    · have heq : q = m - 1 := by omega
      rw [if_pos hlast, heq,
        List.getD_append_right _ _ 0 _ (by simp)]
      simp
    · have hlt : q < m - 1 := by omega
      rw [if_neg hlast, List.getD_append _ _ 0 _ (by simp; exact hlt)]
      exact List.getD_replicate t⁻¹ hlt

#assert_trust kernel source_motif_getD
#assert_trust kernel source_bridge_getD

end NLA.MF24
