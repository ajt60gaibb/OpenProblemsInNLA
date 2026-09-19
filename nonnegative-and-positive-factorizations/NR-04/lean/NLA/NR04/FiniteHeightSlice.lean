/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Actual finite convex-hull slicing for the rank-four branch of Matthew J.
Colbrook's NR-04 proof, University of Cambridge. No rank/height existence,
planar cyclic order, or desired eight-vertex bound is assumed or asserted.
-/
import NLA.NR04.SliceRecombination
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace NLA.NR04

abbrev PositiveHeightIndices {k : ℕ} (H : Fin k → ℝ) := {i : Fin k // 0 < H i}
abbrev NegativeHeightIndices {k : ℕ} (H : Fin k → ℝ) := {i : Fin k // H i < 0}
abbrev ZeroHeightIndices {k : ℕ} (H : Fin k → ℝ) := {i : Fin k // H i = 0}

/-- The actual sign partition, including all zero heights. -/
def heightSignEquiv {k : ℕ} (H : Fin k → ℝ) :
    PositiveHeightIndices H ⊕ (NegativeHeightIndices H ⊕ ZeroHeightIndices H) ≃ Fin k where
  toFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  invFun i := if hp : 0 < H i then Sum.inl ⟨i, hp⟩
    else if hn : H i < 0 then Sum.inr (Sum.inl ⟨i, hn⟩)
    else Sum.inr (Sum.inr ⟨i, le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)⟩)
  left_inv := by
    intro ix
    rcases ix with ip | (im | iz)
    · simp [ip.property]
    · have hp : ¬ 0 < H im.val := not_lt_of_ge (le_of_lt im.property)
      simp [hp, im.property]
    · have hp : ¬ 0 < H iz.val := by rw [iz.property]; exact lt_irrefl _
      have hn : ¬ H iz.val < 0 := by rw [iz.property]; exact lt_irrefl _
      simp [hp, hn]
  right_inv := by
    intro i
    by_cases hp : 0 < H i
    · simp [hp]
    · by_cases hn : H i < 0 <;> simp [hp, hn]

/-- All supplied indices occur exactly once in the sign partition. -/
lemma height_partition_card {k : ℕ} (H : Fin k → ℝ) :
    Fintype.card (PositiveHeightIndices H) + Fintype.card (NegativeHeightIndices H) +
      Fintype.card (ZeroHeightIndices H) = k := by
  simpa only [Fintype.card_sum, Fintype.card_fin, add_assoc] using
    Fintype.card_congr (heightSignEquiv H)

/-- Scalar or vector sums may be reindexed by the actual sign partition. -/
lemma sum_height_partition {k : ℕ} {A : Type*} [AddCommMonoid A]
    (H : Fin k → ℝ) (f : Fin k → A) :
    (∑ i : PositiveHeightIndices H, f i.val) +
      (∑ j : NegativeHeightIndices H, f j.val) +
      (∑ l : ZeroHeightIndices H, f l.val) = ∑ i : Fin k, f i := by
  have heq := (heightSignEquiv H).sum_comp f
  simpa only [Fintype.sum_sum_type, heightSignEquiv, Equiv.coe_fn_mk,
    Sum.elim_inl, Sum.elim_inr, add_assoc] using heq

def positiveHeightEnumeration {k : ℕ} (H : Fin k → ℝ) :
    Fin (Fintype.card (PositiveHeightIndices H)) ≃ PositiveHeightIndices H :=
  (Fintype.equivFin (PositiveHeightIndices H)).symm

def negativeHeightEnumeration {k : ℕ} (H : Fin k → ℝ) :
    Fin (Fintype.card (NegativeHeightIndices H)) ≃ NegativeHeightIndices H :=
  (Fintype.equivFin (NegativeHeightIndices H)).symm

def zeroHeightEnumeration {k : ℕ} (H : Fin k → ℝ) :
    Fin (Fintype.card (ZeroHeightIndices H)) ≃ ZeroHeightIndices H :=
  (Fintype.equivFin (ZeroHeightIndices H)).symm

/-- Finite index enumerations preserve the same split sums; they add no
surrogate points and make no injectivity assumption on the point family. -/
lemma sum_height_partition_fin {k : ℕ} {A : Type*} [AddCommMonoid A]
    (H : Fin k → ℝ) (f : Fin k → A) :
    (∑ i, f (positiveHeightEnumeration H i).val) +
      (∑ j, f (negativeHeightEnumeration H j).val) +
      (∑ l, f (zeroHeightEnumeration H l).val) = ∑ i : Fin k, f i := by
  rw [(positiveHeightEnumeration H).sum_comp (fun i => f i.val),
    (negativeHeightEnumeration H).sum_comp (fun j => f j.val),
    (zeroHeightEnumeration H).sum_comp (fun l => f l.val)]
  exact sum_height_partition H f

/-- Every point of a finite family's convex hull has normalized nonnegative
weights on that very family, retaining duplicate and zero-weight generators. -/
lemma mem_finite_range_convexHull_weights {N k : ℕ}
    (v : Fin k → Fin N → ℝ) (x : Fin N → ℝ)
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = 1 ∧
      (∑ i, c i • v i) = x := by
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, c, hc, hsum, hpoint⟩ := hx
  let w : Fin k → ℝ := fun i => if i ∈ s then c i else 0
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simpa [w, hi] using hc i hi
    · simp [w, hi]
  · simpa [w] using hsum
  · calc
      (∑ i, w i • v i) = ∑ i ∈ s, c i • v i := by simp [w, ite_smul]
      _ = s.affineCombination ℝ v c :=
        (Finset.affineCombination_eq_linear_combination s v c hsum).symm
      _ = x := hpoint

/-- Actual zero-height generators and actual crossings of opposite-height
generators. The enclosing space and the linear map are unchanged. -/
def heightSliceCandidates {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) : Set (Fin N → ℝ) :=
  Set.range (fun l : ZeroHeightIndices (fun i => h (v i)) => v l.val) ∪
    Set.range (fun ij : PositiveHeightIndices (fun i => h (v i)) ×
        NegativeHeightIndices (fun i => h (v i)) =>
      sliceCrossPoint (h (v ij.1.val)) (-h (v ij.2.val)) (v ij.1.val) (v ij.2.val))

/-- Forward slice inclusion, using arbitrary convex coefficients on the
original finite family and the proved zero- and positive-mass recombination. -/
lemma finite_height_slice_subset {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) :
    convexHull ℝ (Set.range v) ∩ {x | h x = 0} ⊆
      convexHull ℝ (heightSliceCandidates h v) := by
  rintro x ⟨hx, hxzero⟩
  obtain ⟨c, hc, hc1, hcx⟩ := mem_finite_range_convexHull_weights v x hx
  let H : Fin k → ℝ := fun i => h (v i)
  let ep := positiveHeightEnumeration H
  let en := negativeHeightEnumeration H
  let ez := zeroHeightEnumeration H
  let a := fun i => H (ep i).val
  let b := fun j => -H (en j).val
  let t := fun i => c (ep i).val
  let s := fun j => c (en j).val
  let r := fun l => c (ez l).val
  let u := fun i => v (ep i).val
  let vn := fun j => v (en j).val
  let w := fun l => v (ez l).val
  have ha : ∀ i, 0 < a i := fun i => (ep i).property
  have hb : ∀ j, 0 < b j := fun j => neg_pos.mpr (en j).property
  have hsum : (∑ i, t i) + (∑ j, s j) + (∑ l, r l) = 1 := by
    change (∑ i, c (positiveHeightEnumeration H i).val) +
      (∑ j, c (negativeHeightEnumeration H j).val) +
      (∑ l, c (zeroHeightEnumeration H l).val) = 1
    rw [sum_height_partition_fin, hc1]
  have hpoint : (∑ i, t i • u i) + (∑ j, s j • vn j) + (∑ l, r l • w l) = x := by
    change (∑ i, c (positiveHeightEnumeration H i).val • v (positiveHeightEnumeration H i).val) +
      (∑ j, c (negativeHeightEnumeration H j).val • v (negativeHeightEnumeration H j).val) +
      (∑ l, c (zeroHeightEnumeration H l).val • v (zeroHeightEnumeration H l).val) = x
    rw [sum_height_partition_fin H (fun i => c i • v i), hcx]
  have hmem := height_zero_combination_mem_slice_hull h a t b s r u vn w
    ha hb (fun i => hc _) (fun j => hc _) (fun l => hc _) hsum
    (fun i => rfl) (fun j => by simp [vn, b, H])
    (fun l => (ez l).property) (by rw [hpoint]; exact hxzero)
  rw [hpoint] at hmem
  apply (convexHull_mono ?_) hmem
  rintro y (⟨l, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
  · exact Or.inl ⟨ez l, rfl⟩
  · exact Or.inr ⟨(ep i, en j), rfl⟩

/-- Exact finite-hull slice representation. Empty/one-sided families and
empty slices are included; no existence of a rank-derived height is assumed. -/
lemma finite_height_slice_eq {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) :
    convexHull ℝ (Set.range v) ∩ {x | h x = 0} =
      convexHull ℝ (heightSliceCandidates h v) := by
  apply Set.Subset.antisymm (finite_height_slice_subset h v)
  apply convexHull_min
  · rintro y (⟨l, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
    · exact ⟨subset_convexHull ℝ (Set.range v) ⟨l.val, rfl⟩, l.property⟩
    · refine ⟨slice_cross_mem_convexHull (Set.range v) _ _ _ _
        i.property (neg_pos.mpr j.property) ⟨i.val, rfl⟩ ⟨j.val, rfl⟩, ?_⟩
      exact slice_cross_height_zero h _ _ _ _ rfl (by simp)
  · exact (convex_convexHull ℝ (Set.range v)).inter h.ker.convex

#print axioms height_partition_card
#print axioms sum_height_partition_fin
#print axioms mem_finite_range_convexHull_weights
#print axioms finite_height_slice_eq

end NLA.NR04
