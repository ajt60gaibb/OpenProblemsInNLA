/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Internal geometric prerequisite for Matthew J. Colbrook's NR-04 proof,
University of Cambridge. This proves finiteness of the ACTUAL extreme points
of an affine section of a finite convex hull, then its exact extreme-point
hull representation. No substitute polygon or geometric oracle is assumed.

The finite-support argument does not require generic position, minimal
representations, affine independence, a nonempty section, or a dimension
restriction. Topology is used only for the final Krein--Milman step.
-/
import NLA.NR04.Definitions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace NLA.NR04

/-- A positive number uniformly smaller than a finite family of positive
numbers, with an additional fixed upper bound of one half. -/
private lemma finite_positive_step {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ ∀ i ∈ s, d ≤ f i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
      simp
  | @insert a s ha ih =>
      intro hf
      obtain ⟨d, hd, hdhalf, hds⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      refine ⟨min d (f a), lt_min hd (hf a (Finset.mem_insert_self a s)),
        (min_le_left _ _).trans hdhalf, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hds i hi)

/-- An extreme point of a finite convex hull cut by an affine subspace
cannot share its positive coefficient support with a different point of
that same affine cut. In fact, support inclusion already suffices. -/
lemma extreme_eq_of_weight_support_subset {N : ℕ}
    (s : Finset (Fin N → ℝ)) (L : AffineSubspace ℝ (Fin N → ℝ))
    (x y : Fin N → ℝ)
    (hx : x ∈ (convexHull ℝ (s : Set (Fin N → ℝ)) ∩ (L : Set (Fin N → ℝ))).extremePoints ℝ)
    (hyL : y ∈ L)
    (wx wy : (Fin N → ℝ) → ℝ)
    (hwx0 : ∀ a ∈ s, 0 ≤ wx a) (hwy0 : ∀ a ∈ s, 0 ≤ wy a)
    (hwx1 : ∑ a ∈ s, wx a = 1) (hwy1 : ∑ a ∈ s, wy a = 1)
    (hwxx : ∑ a ∈ s, wx a • a = x) (hwyy : ∑ a ∈ s, wy a • a = y)
    (hsupport : ∀ a ∈ s, 0 < wy a → 0 < wx a) : y = x := by
  classical
  obtain ⟨d, hd, hdhalf, hdle⟩ := finite_positive_step
    (s.filter fun a => 0 < wx a) wx (fun a ha => (Finset.mem_filter.mp ha).2)
  have hden : 0 < 1 - d := by linarith
  have hwy_le (a : Fin N → ℝ) (ha : a ∈ s) : wy a ≤ 1 := by
    rw [← hwy1]
    exact Finset.single_le_sum hwy0 ha
  let wz (a : Fin N → ℝ) : ℝ := (wx a - d * wy a) / (1 - d)
  let z : Fin N → ℝ := fun i => (x i - d * y i) / (1 - d)
  have hwz0 (a : Fin N → ℝ) (ha : a ∈ s) : 0 ≤ wz a := by
    apply div_nonneg _ hden.le
    by_cases hp : 0 < wx a
    · have hda : d ≤ wx a := hdle a (Finset.mem_filter.mpr ⟨ha, hp⟩)
      have hprod : d * wy a ≤ d := by
        simpa using mul_le_mul_of_nonneg_left (hwy_le a ha) hd.le
      linarith
    · have hxzero : wx a = 0 := le_antisymm (le_of_not_gt hp) (hwx0 a ha)
      have hyzero : wy a = 0 := by
        apply le_antisymm _ (hwy0 a ha)
        exact le_of_not_gt (fun h => hp (hsupport a ha h))
      simp [hxzero, hyzero]
  have hwz1 : ∑ a ∈ s, wz a = 1 := by
    simp only [wz]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hwx1, hwy1]
    simp [ne_of_gt hden]
  have hwzz : ∑ a ∈ s, wz a • a = z := by
    ext i
    have hxi : ∑ a ∈ s, wx a * a i = x i := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hwxx i
    have hyi : ∑ a ∈ s, wy a * a i = y i := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hwyy i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ a ∈ s, ((wx a - d * wy a) / (1 - d)) * a i) =
      (x i - d * y i) / (1 - d)
    calc
      (∑ a ∈ s, ((wx a - d * wy a) / (1 - d)) * a i) =
          (∑ a ∈ s, (wx a * a i - d * (wy a * a i))) / (1 - d) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (x i - d * y i) / (1 - d) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hxi, hyi]
  have hzL : z ∈ L := by
    have hz : z = (1 / (1 - d)) • (x - y) + y := by
      ext i
      simp only [z, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp [ne_of_gt hden] <;> ring
    rw [hz]
    exact L.smul_vsub_vadd_mem (1 / (1 - d)) hx.1.2 hyL hyL
  have hzS : z ∈ convexHull ℝ (s : Set (Fin N → ℝ)) :=
    Finset.mem_convexHull'.mpr ⟨wz, hwz0, hwz1, hwzz⟩
  have hyS : y ∈ convexHull ℝ (s : Set (Fin N → ℝ)) :=
    Finset.mem_convexHull'.mpr ⟨wy, hwy0, hwy1, hwyy⟩
  apply hx.2 ⟨hyS, hyL⟩ ⟨hzS, hzL⟩
  refine ⟨d, 1 - d, hd, hden, by ring, ?_⟩
  ext i
  simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hden] <;> ring

/-- Every affine section of a finite convex hull has finitely many actual
extreme points. The empty section is included. -/
lemma finite_extremePoints_affine_section {N : ℕ}
    (s : Finset (Fin N → ℝ)) (L : AffineSubspace ℝ (Fin N → ℝ)) :
    ((convexHull ℝ (s : Set (Fin N → ℝ)) ∩ (L : Set (Fin N → ℝ))).extremePoints ℝ).Finite := by
  classical
  let E : Set (Fin N → ℝ) :=
    (convexHull ℝ (s : Set (Fin N → ℝ)) ∩ (L : Set (Fin N → ℝ))).extremePoints ℝ
  have hrep : ∀ x : E, ∃ w : (Fin N → ℝ) → ℝ,
      (∀ a ∈ s, 0 ≤ w a) ∧ (∑ a ∈ s, w a = 1) ∧ (∑ a ∈ s, w a • a = x.val) := by
    intro x
    exact Finset.mem_convexHull'.mp x.property.1.1
  choose w hw0 hw1 hwx using hrep
  let support (x : E) : Finset s := Finset.univ.filter fun a => 0 < w x a.val
  have hinj : Function.Injective support := by
    intro x y hxy
    apply Subtype.ext
    symm
    apply extreme_eq_of_weight_support_subset s L x.val y.val x.property y.property.1.2
      (w x) (w y) (hw0 x) (hw0 y) (hw1 x) (hw1 y) (hwx x) (hwx y)
    intro a ha hya
    have hay : (⟨a, ha⟩ : s) ∈ support y := by simp [support, hya]
    rw [← hxy] at hay
    simpa [support] using hay
  haveI : Finite E := Finite.of_injective support hinj
  exact Set.finite_coe_iff.mp inferInstance

/-- Exact finite extreme-point hull representation of an affine section.
Krein--Milman gives the closed convex hull; finiteness proves that closure
is redundant. No unproved Minkowski--Weyl interface is used. -/
lemma convexHull_extremePoints_affine_section {N : ℕ}
    (s : Finset (Fin N → ℝ)) (L : AffineSubspace ℝ (Fin N → ℝ)) :
    convexHull ℝ ((convexHull ℝ (s : Set (Fin N → ℝ)) ∩
      (L : Set (Fin N → ℝ))).extremePoints ℝ) =
      convexHull ℝ (s : Set (Fin N → ℝ)) ∩ (L : Set (Fin N → ℝ)) := by
  have hf := finite_extremePoints_affine_section s L
  have hc : IsCompact (convexHull ℝ (s : Set (Fin N → ℝ)) ∩
      (L : Set (Fin N → ℝ))) :=
    (s.finite_toSet.isCompact_convexHull ℝ).inter_right L.closed_of_finiteDimensional
  have hconv := (convex_convexHull ℝ (s : Set (Fin N → ℝ))).inter L.convex
  have hkm := closure_convexHull_extremePoints hc hconv
  rw [(hf.isClosed_convexHull ℝ).closure_eq] at hkm
  exact hkm

#print axioms extreme_eq_of_weight_support_subset
#print axioms finite_extremePoints_affine_section
#print axioms convexHull_extremePoints_affine_section

end NLA.NR04
