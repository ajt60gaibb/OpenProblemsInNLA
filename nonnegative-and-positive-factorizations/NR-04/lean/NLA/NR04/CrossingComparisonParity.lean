/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Exact integer comparison identities for Matthew J. Colbrook's NR-04 argument,
University of Cambridge. Only ordinary order regions are used; no permutation
enumeration or numerical evaluation occurs.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.WithBot
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

/-- The actual integer indicator of a strict comparison between constructed keys. -/
def keyIndicator (a b : WithBot ℝ) : ℤ := if a < b then 1 else 0

lemma key_indicator_reverse (a b : WithBot ℝ) (hab : a ≠ b) :
    keyIndicator a b = 1 - keyIndicator b a := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · simp [keyIndicator, hlt, not_lt_of_gt hlt]
  · simp [keyIndicator, hgt, not_lt_of_gt hgt]

lemma key_indicator_pair_left (a b c : WithBot ℝ) (hab : a < b) (hca : c < a) :
    keyIndicator a c + keyIndicator b c = 0 := by
  have hcb : c < b := hca.trans hab
  simp [keyIndicator, not_lt_of_gt hca, not_lt_of_gt hcb]

lemma key_indicator_pair_middle (a b c : WithBot ℝ) (hac : a < c) (hcb : c < b) :
    keyIndicator a c + keyIndicator b c = 1 := by
  simp [keyIndicator, hac, not_lt_of_gt hcb]

lemma key_indicator_pair_right (a b c : WithBot ℝ) (hab : a < b) (hbc : b < c) :
    keyIndicator a c + keyIndicator b c = 2 := by
  simp [keyIndicator, hbc, hab.trans hbc]

lemma key_indicator_sum_odd_of_one_between (a b c d : WithBot ℝ)
    (hac : a < c) (hcb : c < b) (hda : d ≠ a) (hdb : d ≠ b)
    (hd : ¬ (a < d ∧ d < b)) :
    Odd (keyIndicator a c + keyIndicator a d + keyIndicator b c + keyIndicator b d) := by
  have hab : a < b := hac.trans hcb
  have hgroup : keyIndicator a c + keyIndicator a d + keyIndicator b c + keyIndicator b d =
      (keyIndicator a c + keyIndicator b c) + (keyIndicator a d + keyIndicator b d) := by
    ring
  rw [hgroup, key_indicator_pair_middle a b c hac hcb]
  rcases lt_trichotomy d a with hlt | heq | hgt
  · rw [key_indicator_pair_left a b d hab hlt]
    exact ⟨0, by ring⟩
  · exact False.elim (hda heq)
  · have hbd : b < d := by
      rcases lt_trichotomy d b with hlt' | heq' | hgt'
      · exact False.elim (hd ⟨hgt, hlt'⟩)
      · exact False.elim (hdb heq')
      · exact hgt'
    rw [key_indicator_pair_right a b d hab hbd]
    exact ⟨1, by ring⟩

#print axioms key_indicator_reverse
#print axioms key_indicator_pair_left
#print axioms key_indicator_pair_middle
#print axioms key_indicator_pair_right
#print axioms key_indicator_sum_odd_of_one_between
#assert_trust kernel key_indicator_reverse
#assert_trust kernel key_indicator_pair_left
#assert_trust kernel key_indicator_pair_middle
#assert_trust kernel key_indicator_pair_right
#assert_trust kernel key_indicator_sum_odd_of_one_between

end NLA.NR04
