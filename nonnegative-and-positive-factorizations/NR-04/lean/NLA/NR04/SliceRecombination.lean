/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Finite algebra for the rank-four branch of Matthew J. Colbrook's NR-04 proof,
University of Cambridge. This does not assert frozen C08 or a planar vertex
bound. The source-only author's statement-first plan is STATEMENT-FIRST.md.
-/
import NLA.NR04.Definitions
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NLA.NR04

/-- The actual zero-height crossing of points of heights `a` and `-b`.
All uses requiring convexity will prove `a > 0` and `b > 0`. -/
def sliceCrossPoint {N : ℕ} (a b : ℝ) (u v : Fin N → ℝ) : Fin N → ℝ :=
  (b / (a + b)) • u + (a / (a + b)) • v

/-- Explicit recombination coefficient when the balanced height mass is positive. -/
def sliceCrossWeight (M t s a b : ℝ) : ℝ := t * s * (a + b) / M

/-- Finite separated-product algebra, including empty index types. -/
lemma slice_sum_separated {p q : ℕ} (f : Fin p → ℝ) (g : Fin q → ℝ) :
    (∑ i : Fin p, ∑ j : Fin q, f i * g j) =
      (∑ i : Fin p, f i) * ∑ j : Fin q, g j := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- The crossing coefficients preserve the total weight on the two sides. -/
lemma slice_cross_weight_sum {p q : ℕ} (a t : Fin p → ℝ) (b s : Fin q → ℝ)
    (M : ℝ) (hM : 0 < M)
    (ht : (∑ i, t i * a i) = M) (hs : (∑ j, s j * b j) = M) :
    (∑ i : Fin p, ∑ j : Fin q, sliceCrossWeight M (t i) (s j) (a i) (b j)) =
      (∑ i, t i) + ∑ j, s j := by
  have hraw : (∑ i : Fin p, ∑ j : Fin q, t i * s j * (a i + b j)) =
      (∑ i, t i * a i) * (∑ j, s j) +
        (∑ i, t i) * (∑ j, s j * b j) := by
    calc
      _ = ∑ i : Fin p, ∑ j : Fin q,
          ((t i * a i) * s j + t i * (s j * b j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        rw [slice_sum_separated, slice_sum_separated]
  unfold sliceCrossWeight
  simp_rw [← Finset.sum_div]
  rw [hraw, ht, hs]
  field_simp [ne_of_gt hM]
  ring

/-- Exact scalar barycenter identity. Positivity is used only to justify
the genuine crossing denominator; no vector-geometry assertion is assumed. -/
lemma slice_cross_scalar_sum {p q : ℕ}
    (a t u : Fin p → ℝ) (b s v : Fin q → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (M : ℝ) (hM : 0 < M)
    (ht : (∑ i, t i * a i) = M) (hs : (∑ j, s j * b j) = M) :
    (∑ i : Fin p, ∑ j : Fin q,
      sliceCrossWeight M (t i) (s j) (a i) (b j) *
        ((b j / (a i + b j)) * u i + (a i / (a i + b j)) * v j)) =
      (∑ i, t i * u i) + ∑ j, s j * v j := by
  have hterm (i : Fin p) (j : Fin q) :
      sliceCrossWeight M (t i) (s j) (a i) (b j) *
        ((b j / (a i + b j)) * u i + (a i / (a i + b j)) * v j) =
      ((t i * u i) * (s j * b j) + (t i * a i) * (s j * v j)) / M := by
    unfold sliceCrossWeight
    field_simp [ne_of_gt hM, ne_of_gt (add_pos (ha i) (hb j))]
  simp_rw [hterm, ← Finset.sum_div]
  have hraw : (∑ i : Fin p, ∑ j : Fin q,
      ((t i * u i) * (s j * b j) + (t i * a i) * (s j * v j))) =
      (∑ i, t i * u i) * M + M * (∑ j, s j * v j) := by
    simp_rw [Finset.sum_add_distrib]
    rw [slice_sum_separated, slice_sum_separated, ht, hs]
  rw [hraw]
  field_simp [ne_of_gt hM]

/-- Coordinatewise scalar recombination gives equality of the actual vectors. -/
lemma slice_cross_vector_sum {N p q : ℕ}
    (a t : Fin p → ℝ) (b s : Fin q → ℝ)
    (u : Fin p → Fin N → ℝ) (v : Fin q → Fin N → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (M : ℝ) (hM : 0 < M)
    (ht : (∑ i, t i * a i) = M) (hs : (∑ j, s j * b j) = M) :
    (∑ i : Fin p, ∑ j : Fin q,
      sliceCrossWeight M (t i) (s j) (a i) (b j) •
        sliceCrossPoint (a i) (b j) (u i) (v j)) =
      (∑ i, t i • u i) + ∑ j, s j • v j := by
  ext r
  simpa only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    sliceCrossPoint] using
    slice_cross_scalar_sum a t (fun i => u i r) b s (fun j => v j r)
      ha hb M hM ht hs

/-- The zero-mass case: strict heights and nonnegative weights leave no
weight on that side. This also covers an empty side. -/
lemma slice_weights_zero_of_mass_zero {p : ℕ} (a t : Fin p → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 ≤ t i)
    (hm : (∑ i, t i * a i) = 0) : ∀ i, t i = 0 := by
  intro i
  have hle : t i * a i ≤ ∑ j, t j * a j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (ht j) (ha j).le)
      (Finset.mem_univ i)
  rw [hm] at hle
  have hp : t i * a i = 0 :=
    le_antisymm hle (mul_nonneg (ht i) (ha i).le)
  exact (mul_eq_zero.mp hp).resolve_right (ne_of_gt (ha i))

/-- Balanced combinations lie in the convex hull of zero-height generators
and actual crossings. No height, rank, planar ordering, or vertex-count oracle
appears in the proof: the coefficient identities above supply the inclusion.
All three family sizes may be zero, and repeated points are permitted. -/
lemma balanced_slice_mem_hull {N p q z : ℕ}
    (a t : Fin p → ℝ) (b s : Fin q → ℝ) (r : Fin z → ℝ)
    (u : Fin p → Fin N → ℝ) (v : Fin q → Fin N → ℝ)
    (w : Fin z → Fin N → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (ht : ∀ i, 0 ≤ t i) (hs : ∀ j, 0 ≤ s j) (hr : ∀ l, 0 ≤ r l)
    (hsum : (∑ i, t i) + (∑ j, s j) + (∑ l, r l) = 1)
    (hbalance : (∑ i, t i * a i) = ∑ j, s j * b j) :
    (∑ i, t i • u i) + (∑ j, s j • v j) + (∑ l, r l • w l) ∈
      convexHull ℝ (Set.range w ∪ Set.range
        (fun ij : Fin p × Fin q => sliceCrossPoint (a ij.1) (b ij.2) (u ij.1) (v ij.2))) := by
  classical
  let M : ℝ := ∑ i, t i * a i
  have hMnonneg : 0 ≤ M :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ht i) (ha i).le)
  have htM : (∑ i, t i * a i) = M := rfl
  have hsM : (∑ j, s j * b j) = M := hbalance.symm
  by_cases hMzero : M = 0
  · have htzero : ∀ i, t i = 0 :=
      slice_weights_zero_of_mass_zero a t ha ht (htM.trans hMzero)
    have hszero : ∀ j, s j = 0 :=
      slice_weights_zero_of_mass_zero b s hb hs (hsM.trans hMzero)
    have hsumr : (∑ l, r l) = 1 := by simpa [htzero, hszero] using hsum
    have hmem : (∑ l, r l • w l) ∈
        convexHull ℝ (Set.range w ∪ Set.range
          (fun ij : Fin p × Fin q =>
            sliceCrossPoint (a ij.1) (b ij.2) (u ij.1) (v ij.2))) := by
      exact mem_convexHull_of_exists_fintype r w hr hsumr
        (fun l => Or.inl ⟨l, rfl⟩) rfl
    simpa [htzero, hszero] using hmem
  · have hM : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hMzero)
    let d : Fin p × Fin q → ℝ := fun ij =>
      sliceCrossWeight M (t ij.1) (s ij.2) (a ij.1) (b ij.2)
    let weights : Fin z ⊕ (Fin p × Fin q) → ℝ := Sum.elim r d
    let points : Fin z ⊕ (Fin p × Fin q) → Fin N → ℝ :=
      Sum.elim w (fun ij => sliceCrossPoint (a ij.1) (b ij.2) (u ij.1) (v ij.2))
    have hdnonneg : ∀ ij, 0 ≤ d ij := by
      intro ij
      exact div_nonneg
        (mul_nonneg (mul_nonneg (ht ij.1) (hs ij.2))
          (add_pos (ha ij.1) (hb ij.2)).le) hM.le
    have hdsum : (∑ ij, d ij) = (∑ i, t i) + ∑ j, s j := by
      simpa only [d, Fintype.sum_prod_type] using
        slice_cross_weight_sum a t b s M hM htM hsM
    apply mem_convexHull_of_exists_fintype weights points
    · intro ix
      cases ix with
      | inl l => exact hr l
      | inr ij => exact hdnonneg ij
    · change (∑ ix, Sum.elim r d ix) = 1
      rw [Fintype.sum_sumElim, hdsum]
      linarith
    · intro ix
      cases ix with
      | inl l => exact Or.inl ⟨l, rfl⟩
      | inr ij => exact Or.inr ⟨ij, rfl⟩
    · simp only [weights, points, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.sum_prod_type]
      change (∑ l, r l • w l) +
          (∑ i : Fin p, ∑ j : Fin q,
            sliceCrossWeight M (t i) (s j) (a i) (b j) •
              sliceCrossPoint (a i) (b j) (u i) (v j)) = _
      rw [slice_cross_vector_sum a t b s u v ha hb M hM htM hsM]
      exact add_comm _ _

/-- Every candidate is an actual convex combination of its two endpoints. -/
lemma slice_cross_mem_convexHull {N : ℕ} (S : Set (Fin N → ℝ))
    (a b : ℝ) (u v : Fin N → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hu : u ∈ S) (hv : v ∈ S) :
    sliceCrossPoint a b u v ∈ convexHull ℝ S := by
  have hab : 0 < a + b := add_pos ha hb
  have hsum : b / (a + b) + a / (a + b) = 1 := by
    field_simp [ne_of_gt hab]
    ring
  exact (convex_convexHull ℝ S) (subset_convexHull ℝ S hu) (subset_convexHull ℝ S hv)
    (div_nonneg hb.le hab.le) (div_nonneg ha.le hab.le) hsum

/-- The candidate has height zero for the actual linear height map. -/
lemma slice_cross_height_zero {N : ℕ} (h : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (a b : ℝ) (u v : Fin N → ℝ) (hu : h u = a) (hv : h v = -b) :
    h (sliceCrossPoint a b u v) = 0 := by
  simp only [sliceCrossPoint, map_add, map_smul, hu, hv, smul_eq_mul]
  ring

/-- Applying an actual linear height to a zero-height combination supplies
the balance premise; the balance is not a geometric oracle. -/
lemma slice_balance_of_height_zero {N p q z : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (a t : Fin p → ℝ) (b s : Fin q → ℝ) (r : Fin z → ℝ)
    (u : Fin p → Fin N → ℝ) (v : Fin q → Fin N → ℝ)
    (w : Fin z → Fin N → ℝ)
    (hu : ∀ i, h (u i) = a i) (hv : ∀ j, h (v j) = -b j)
    (hw : ∀ l, h (w l) = 0)
    (hzero : h ((∑ i, t i • u i) + (∑ j, s j • v j) + (∑ l, r l • w l)) = 0) :
    (∑ i, t i * a i) = ∑ j, s j * b j := by
  have heq : h ((∑ i, t i • u i) + (∑ j, s j • v j) + (∑ l, r l • w l)) =
      (∑ i, t i * a i) - ∑ j, s j * b j := by
    simp only [map_add, map_sum, map_smul, hu, hv, hw, smul_eq_mul, mul_neg,
      Finset.sum_neg_distrib, mul_zero, Finset.sum_const_zero, add_zero, sub_eq_add_neg]
  exact sub_eq_zero.mp (heq.symm.trans hzero)

/-- A genuine zero-height convex combination has the crossing-hull
representation, with all coefficient and zero-mass cases proved internally. -/
lemma height_zero_combination_mem_slice_hull {N p q z : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (a t : Fin p → ℝ) (b s : Fin q → ℝ) (r : Fin z → ℝ)
    (u : Fin p → Fin N → ℝ) (v : Fin q → Fin N → ℝ)
    (w : Fin z → Fin N → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (ht : ∀ i, 0 ≤ t i) (hs : ∀ j, 0 ≤ s j) (hr : ∀ l, 0 ≤ r l)
    (hsum : (∑ i, t i) + (∑ j, s j) + (∑ l, r l) = 1)
    (hu : ∀ i, h (u i) = a i) (hv : ∀ j, h (v j) = -b j)
    (hw : ∀ l, h (w l) = 0)
    (hzero : h ((∑ i, t i • u i) + (∑ j, s j • v j) + (∑ l, r l • w l)) = 0) :
    (∑ i, t i • u i) + (∑ j, s j • v j) + (∑ l, r l • w l) ∈
      convexHull ℝ (Set.range w ∪ Set.range
        (fun ij : Fin p × Fin q => sliceCrossPoint (a ij.1) (b ij.2) (u ij.1) (v ij.2))) := by
  exact balanced_slice_mem_hull a t b s r u v w ha hb ht hs hr hsum
    (slice_balance_of_height_zero h a t b s r u v w hu hv hw hzero)

#print axioms slice_cross_weight_sum
#print axioms slice_cross_vector_sum
#print axioms balanced_slice_mem_hull
#print axioms slice_cross_mem_convexHull
#print axioms slice_cross_height_zero
#print axioms slice_balance_of_height_zero
#print axioms height_zero_combination_mem_slice_hull

end NLA.NR04
