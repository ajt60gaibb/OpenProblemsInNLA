/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Order-region determinant signs in the planar implementation of Matthew J.
Colbrook's NR-04 argument, University of Cambridge. The increasing-key
orientation premise is provided by the previously constructed normalization.
-/
import NLA.NR04.PlaneCrossingOrientation
import Mathlib.Order.WithBot

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

lemma plane_orientation_key_regions {ι : Type*}
    (w : ι → Fin 2 → ℝ) (key : ι → WithBot ℝ) (hkey : Function.Injective key)
    (hor : ∀ i j k, key i < key j → key j < key k →
      0 < planeOrientation (w i) (w j) (w k))
    (a b c : ι) (hab : key a < key b) (hca : c ≠ a) (hcb : c ≠ b) :
    (key c < key a ∧ 0 < planeOrientation (w a) (w b) (w c)) ∨
    (key a < key c ∧ key c < key b ∧ planeOrientation (w a) (w b) (w c) < 0) ∨
    (key b < key c ∧ 0 < planeOrientation (w a) (w b) (w c)) := by
  rcases lt_trichotomy (key c) (key a) with hlt | heq | hgt
  · have hp := hor c a b hlt hab
    rw [plane_orientation_cyclic (w c) (w a) (w b)] at hp
    exact Or.inl ⟨hlt, hp⟩
  · exact False.elim (hca (hkey heq))
  · rcases lt_trichotomy (key c) (key b) with hlt' | heq' | hgt'
    · have hp := hor a c b hgt hlt'
      have hswap := plane_orientation_swap_last (w a) (w b) (w c)
      exact Or.inr (Or.inl ⟨hgt, hlt', by linarith only [hp, hswap]⟩)
    · exact False.elim (hcb (hkey heq'))
    · exact Or.inr (Or.inr ⟨hgt', hor a b c hab hgt'⟩)

lemma plane_orientation_negative_iff_between {ι : Type*}
    (w : ι → Fin 2 → ℝ) (key : ι → WithBot ℝ) (hkey : Function.Injective key)
    (hor : ∀ i j k, key i < key j → key j < key k →
      0 < planeOrientation (w i) (w j) (w k))
    (a b c : ι) (hab : key a < key b) (hca : c ≠ a) (hcb : c ≠ b) :
    planeOrientation (w a) (w b) (w c) < 0 ↔ key a < key c ∧ key c < key b := by
  rcases plane_orientation_key_regions w key hkey hor a b c hab hca hcb with
    ⟨hleft, hpos⟩ | ⟨hac, hcb', hneg⟩ | ⟨hright, hpos⟩
  · constructor
    · intro hneg
      exfalso
      linarith only [hpos, hneg]
    · intro hbetween
      exact False.elim (lt_asymm hleft hbetween.1)
  · exact ⟨fun _ => ⟨hac, hcb'⟩, fun _ => hneg⟩
  · constructor
    · intro hneg
      exfalso
      linarith only [hpos, hneg]
    · intro hbetween
      exact False.elim (lt_asymm hright hbetween.2)

lemma plane_orientation_ne_zero_of_key_order {ι : Type*}
    (w : ι → Fin 2 → ℝ) (key : ι → WithBot ℝ) (hkey : Function.Injective key)
    (hor : ∀ i j k, key i < key j → key j < key k →
      0 < planeOrientation (w i) (w j) (w k))
    (a b c : ι) (hab : key a < key b) (hca : c ≠ a) (hcb : c ≠ b) :
    planeOrientation (w a) (w b) (w c) ≠ 0 := by
  rcases plane_orientation_key_regions w key hkey hor a b c hab hca hcb with
    ⟨_, hp⟩ | ⟨_, _, hn⟩ | ⟨_, hp⟩
  · exact ne_of_gt hp
  · exact ne_of_lt hn
  · exact ne_of_gt hp

#print axioms plane_orientation_key_regions
#print axioms plane_orientation_negative_iff_between
#print axioms plane_orientation_ne_zero_of_key_order
#assert_trust kernel plane_orientation_key_regions
#assert_trust kernel plane_orientation_negative_iff_between
#assert_trust kernel plane_orientation_ne_zero_of_key_order

end NLA.NR04
