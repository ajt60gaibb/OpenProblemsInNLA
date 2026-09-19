/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual four-endpoint crossing parity in the planar implementation of Matthew J.
Colbrook's NR-04 argument, University of Cambridge. The key orientation premise
is constructed in PlaneKeyNormalization. No polygon order is postulated.
-/
import NLA.NR04.PlaneKeyOrientationSigns
import NLA.NR04.CrossingComparisonParity

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

lemma ordered_key_crossing_odd {ι : Type*}
    (w : ι → Fin 2 → ℝ) (key : ι → WithBot ℝ) (hkey : Function.Injective key)
    (hor : ∀ i j k, key i < key j → key j < key k →
      0 < planeOrientation (w i) (w j) (w k))
    (a b c d : ι) (hab : key a < key b)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hcross : (openSegment ℝ (w a) (w b) ∩ openSegment ℝ (w c) (w d)).Nonempty) :
    Odd (keyIndicator (key a) (key c) + keyIndicator (key a) (key d) +
      keyIndicator (key b) (key c) + keyIndicator (key b) (key d)) := by
  have hcne := plane_orientation_ne_zero_of_key_order w key hkey hor a b c hab hca hcb
  have hciff := plane_orientation_negative_iff_between w key hkey hor a b c hab hca hcb
  have hdiff := plane_orientation_negative_iff_between w key hkey hor a b d hab hda hdb
  have hcan : key c ≠ key a := fun h => hca (hkey h)
  have hcbn : key c ≠ key b := fun h => hcb (hkey h)
  have hdan : key d ≠ key a := fun h => hda (hkey h)
  have hdbn : key d ≠ key b := fun h => hdb (hkey h)
  rcases crossing_orientation_opposite (w a) (w b) (w c) (w d) hcross hcne with
    ⟨hcneg, hdpos⟩ | ⟨hcpos, hdneg⟩
  · have hcbetween := hciff.mp hcneg
    have hdoutside : ¬ (key a < key d ∧ key d < key b) := by
      intro hdinside
      exact (not_lt_of_ge hdpos.le) (hdiff.mpr hdinside)
    exact key_indicator_sum_odd_of_one_between (key a) (key b) (key c) (key d)
      hcbetween.1 hcbetween.2 hdan hdbn hdoutside
  · have hdbetween := hdiff.mp hdneg
    have hcoutside : ¬ (key a < key c ∧ key c < key b) := by
      intro hcinside
      exact (not_lt_of_ge hcpos.le) (hciff.mpr hcinside)
    have hodd := key_indicator_sum_odd_of_one_between (key a) (key b) (key d) (key c)
      hdbetween.1 hdbetween.2 hcan hcbn hcoutside
    have hswap :
        keyIndicator (key a) (key c) + keyIndicator (key a) (key d) +
          keyIndicator (key b) (key c) + keyIndicator (key b) (key d) =
        keyIndicator (key a) (key d) + keyIndicator (key a) (key c) +
          keyIndicator (key b) (key d) + keyIndicator (key b) (key c) := by ring
    rw [hswap]
    exact hodd

/-- Four actual distinct endpoints with intersecting open diagonals have odd
integer comparison parity for the actual constructed orientation key. -/
theorem four_endpoint_crossing_odd {ι : Type*}
    (w : ι → Fin 2 → ℝ) (key : ι → WithBot ℝ) (hkey : Function.Injective key)
    (hor : ∀ i j k, key i < key j → key j < key k →
      0 < planeOrientation (w i) (w j) (w k))
    (a b c d : ι) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (_hcd : c ≠ d)
    (hcross : (openSegment ℝ (w a) (w b) ∩ openSegment ℝ (w c) (w d)).Nonempty) :
    Odd (keyIndicator (key a) (key c) + keyIndicator (key a) (key d) +
      keyIndicator (key b) (key c) + keyIndicator (key b) (key d)) := by
  have habkey : key a ≠ key b := fun h => hab (hkey h)
  rcases lt_or_gt_of_ne habkey with hlt | hgt
  · exact ordered_key_crossing_odd w key hkey hor a b c d hlt
      hac.symm hbc.symm had.symm hbd.symm hcross
  · have hcross' :
        (openSegment ℝ (w b) (w a) ∩ openSegment ℝ (w c) (w d)).Nonempty := by
      rw [openSegment_symm ℝ (w b) (w a)]
      exact hcross
    have hodd := ordered_key_crossing_odd w key hkey hor b a c d hgt
      hbc.symm hac.symm hbd.symm had.symm hcross'
    have hswap :
        keyIndicator (key a) (key c) + keyIndicator (key a) (key d) +
          keyIndicator (key b) (key c) + keyIndicator (key b) (key d) =
        keyIndicator (key b) (key c) + keyIndicator (key b) (key d) +
          keyIndicator (key a) (key c) + keyIndicator (key a) (key d) := by ring
    rw [hswap]
    exact hodd

#print axioms ordered_key_crossing_odd
#print axioms four_endpoint_crossing_odd
#assert_trust kernel ordered_key_crossing_odd
#assert_trust kernel four_endpoint_crossing_odd

end NLA.NR04
