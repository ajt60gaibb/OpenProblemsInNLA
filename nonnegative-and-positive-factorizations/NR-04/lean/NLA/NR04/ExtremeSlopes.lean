/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual distinct-slope geometry in the planar implementation of Matthew J.
Colbrook's NR-04 argument, University of Cambridge. The final bundle constructs
its affine normalization and preserves the actual extreme-point predicates.
No ordering/parity theorem or section vertex bound is assumed.
-/
import NLA.NR04.PlaneShear
import NLA.NR04.ExtremeOrientation
import NLA.NR04.AffinePlaneCoordinates

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

lemma plane_eq_smul_of_slope_eq (p q : Fin 2 → ℝ)
    (hp : 0 < p 0) (hq : 0 < q 0)
    (hs : planeSlope p = planeSlope q) : p = (p 0 / q 0) • q := by
  change p 1 / p 0 = q 1 / q 0 at hs
  have hcross := (div_eq_div_iff (ne_of_gt hp) (ne_of_gt hq)).mp hs
  funext i
  fin_cases i
  · change p 0 = (p 0 / q 0) * q 0
    field_simp [ne_of_gt hq]
  · change p 1 = (p 0 / q 0) * q 1
    field_simp [ne_of_gt hq] <;> nlinarith only [hcross]

lemma not_extreme_of_strict_smul {N : ℕ}
    (S : Set (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ S)
    (p q : Fin N → ℝ) (hq : q ∈ S) (hpne : p ≠ 0)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (heq : p = a • q) :
    p ∉ S.extremePoints ℝ := by
  intro hp
  have hseg : p ∈ openSegment ℝ (0 : Fin N → ℝ) q := by
    refine ⟨1 - a, a, sub_pos.mpr ha1, ha, by ring, ?_⟩
    simpa only [smul_zero, zero_add] using heq.symm
  exact hpne (hp.2 h0 hq hseg).symm

/-- Two actual extreme points on the same positive ray must coincide. -/
lemma extreme_positive_slope_eq
    (S : Set (Fin 2 → ℝ)) (h0 : (0 : Fin 2 → ℝ) ∈ S)
    (p q : Fin 2 → ℝ) (hp : p ∈ S.extremePoints ℝ)
    (hq : q ∈ S.extremePoints ℝ)
    (hpx : 0 < p 0) (hqx : 0 < q 0)
    (hs : planeSlope p = planeSlope q) : p = q := by
  have hpne : p ≠ 0 := by
    intro heq
    have hz := congrFun heq 0
    change p 0 = 0 at hz
    linarith only [hpx, hz]
  have hqne : q ≠ 0 := by
    intro heq
    have hz := congrFun heq 0
    change q 0 = 0 at hz
    linarith only [hqx, hz]
  rcases lt_trichotomy (p 0) (q 0) with hlt | heq | hgt
  · exact False.elim ((not_extreme_of_strict_smul S h0 p q hq.1 hpne
      (p 0 / q 0) (div_pos hpx hqx) ((div_lt_one hqx).mpr hlt)
      (plane_eq_smul_of_slope_eq p q hpx hqx hs)) hp)
  · have hcomb := plane_eq_smul_of_slope_eq p q hpx hqx hs
    rw [heq, div_self (ne_of_gt hqx), one_smul] at hcomb
    exact hcomb
  · exact False.elim ((not_extreme_of_strict_smul S h0 q p hp.1 hqne
      (q 0 / p 0) (div_pos hqx hpx) ((div_lt_one hpx).mpr hgt)
      (plane_eq_smul_of_slope_eq q p hqx hpx hs.symm)) hq)

theorem extreme_nonorigin_slopes_injective {n : ℕ}
    (w : Fin n → Fin 2 → ℝ) (hw : Function.Injective w)
    (i0 : Fin n) (hzero : w i0 = 0)
    (hext : ∀ i, w i ∈ (convexHull ℝ (Set.range w)).extremePoints ℝ)
    (hx : ∀ i, i ≠ i0 → 0 < w i 0) :
    Function.Injective (fun i : {i : Fin n // i ≠ i0} => planeSlope (w i.1)) := by
  have h0 : (0 : Fin 2 → ℝ) ∈ convexHull ℝ (Set.range w) := by
    rw [← hzero]
    exact subset_convexHull ℝ _ (Set.mem_range_self i0)
  intro i j hs
  apply Subtype.ext
  apply hw
  exact extreme_positive_slope_eq (convexHull ℝ (Set.range w)) h0
    (w i.1) (w j.1) (hext i.1) (hext j.1) (hx i.1 i.2) (hx j.1 j.2) hs

/-- Constructed affine normalization of an actual finite extreme family.
The nonorigin slope key is injective; no explicit permutation is enumerated. -/
theorem finite_extreme_family_positive_normalization {n : ℕ}
    (w : Fin n → Fin 2 → ℝ) (hw : Function.Injective w) (hn : 0 < n)
    (hext : ∀ i, w i ∈ (convexHull ℝ (Set.range w)).extremePoints ℝ) :
    ∃ t : ℝ, ∃ i0 : Fin n,
      let z := fun i => planeShearShift t (w i0) (w i)
      z i0 = 0 ∧ Function.Injective z ∧
      (∀ i, i ≠ i0 → 0 < z i 0) ∧
      (∀ i, z i ∈ (convexHull ℝ (Set.range z)).extremePoints ℝ) ∧
      Function.Injective (fun i : {i : Fin n // i ≠ i0} => planeSlope (z i.1)) := by
  obtain ⟨t, i0, hfinj, hzero, hpos, hzinj⟩ :=
    finite_plane_family_positive_shear w hw hn
  let f := planeShearShift t (w i0)
  let z : Fin n → Fin 2 → ℝ := fun i => f (w i)
  have hzr : f '' Set.range w = Set.range z := by
    ext y
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w i, Set.mem_range_self i, rfl⟩
  have hhull : f '' convexHull ℝ (Set.range w) = convexHull ℝ (Set.range z) := by
    rw [f.image_convexHull, hzr]
  have hextz : ∀ i, z i ∈ (convexHull ℝ (Set.range z)).extremePoints ℝ := by
    intro i
    have hz := (affine_injective_extreme_image_iff f hfinj
      (convexHull ℝ (Set.range w)) (w i)).mpr (hext i)
    rw [hhull] at hz
    exact hz
  have hslopes := extreme_nonorigin_slopes_injective z hzinj i0 hzero hextz hpos
  exact ⟨t, i0, hzero, hzinj, hpos, hextz, hslopes⟩

#print axioms plane_eq_smul_of_slope_eq
#print axioms not_extreme_of_strict_smul
#print axioms extreme_positive_slope_eq
#print axioms extreme_nonorigin_slopes_injective
#print axioms finite_extreme_family_positive_normalization
#assert_trust kernel plane_eq_smul_of_slope_eq
#assert_trust kernel not_extreme_of_strict_smul
#assert_trust kernel extreme_positive_slope_eq
#assert_trust kernel extreme_nonorigin_slopes_injective
#assert_trust kernel finite_extreme_family_positive_normalization

end NLA.NR04
