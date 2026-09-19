/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Frozen NR-04 C09, from Matthew J. Colbrook's mathematical proof,
University of Cambridge. The proof enumerates the actual extreme points
of the actual affine section. Its geometric finiteness and hull equality
are derived in FiniteSection; the contact count is derived in IncidenceCount.
No new hypothesis is added to the frozen statement.
-/
import NLA.NR04.FiniteSection
import NLA.NR04.IncidenceCount

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace NLA.NR04

lemma nonnegative_of_mem_columnHull {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : EntrywiseNonnegative U)
    (x : Fin N → ℝ) (hx : x ∈ columnHull U) : ∀ i, 0 ≤ x i := by
  have hcone : Convex ℝ {v : Fin N → ℝ | ∀ i, 0 ≤ v i} := by
    intro a ha b hb c d hc hd hcd i
    exact add_nonneg (mul_nonneg hc (ha i)) (mul_nonneg hd (hb i))
  have hgen : columnSet U ⊆ {v : Fin N → ℝ | ∀ i, 0 ≤ v i} := by
    rintro _ ⟨j, rfl⟩ i
    exact hU i j
  exact (convexHull_min hgen hcone) hx

lemma finite_extremePoints_columnSection {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    ((columnSection U X).extremePoints ℝ).Finite := by
  classical
  let hs : (columnSet U).Finite := Set.finite_range (fun j => fun i => U i j)
  simpa only [Set.Finite.coe_toFinset, columnSection, columnHull] using
    finite_extremePoints_affine_section hs.toFinset (columnAffineSpan X)

lemma convexHull_extremePoints_columnSection {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    convexHull ℝ ((columnSection U X).extremePoints ℝ) = columnSection U X := by
  classical
  let hs : (columnSet U).Finite := Set.finite_range (fun j => fun i => U i j)
  simpa only [Set.Finite.coe_toFinset, columnSection, columnHull] using
    convexHull_extremePoints_affine_section hs.toFinset (columnAffineSpan X)

/-- C09: the source polygon-contact argument, in precisely its needed setting.
There is no restriction on the number or ordinary rank of the outer generators. -/
theorem section_contact_bound {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) (hdiag : ∀ i, X i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < X i j)
    (hcontain : columnSet X ⊆ columnHull U) :
    ((columnSection U X).extremePoints ℝ).Finite ∧
      N ≤ ((columnSection U X).extremePoints ℝ).ncard := by
  classical
  let E : Set (Fin N → ℝ) := (columnSection U X).extremePoints ℝ
  have hf : E.Finite := finite_extremePoints_columnSection U X
  refine ⟨hf, ?_⟩
  let v : Finset (Fin N → ℝ) := hf.toFinset
  have hcoe : (v : Set (Fin N → ℝ)) = E := hf.coe_toFinset
  have hvhull : convexHull ℝ (v : Set (Fin N → ℝ)) = columnSection U X := by
    rw [hcoe]
    exact convexHull_extremePoints_columnSection U X
  have hrep : ∀ j : Fin N, ∃ w : (Fin N → ℝ) → ℝ,
      (∀ a ∈ v, 0 ≤ w a) ∧ (∑ a ∈ v, w a = 1) ∧
      (∑ a ∈ v, w a • a = fun i => X i j) := by
    intro j
    apply Finset.mem_convexHull'.mp
    rw [hvhull]
    exact ⟨hcontain ⟨j, rfl⟩, subset_affineSpan ℝ (columnSet X) ⟨j, rfl⟩⟩
  choose w hw0 hw1 hwx using hrep
  let e : Fin v.card ≃ v := v.equivFin.symm
  let V : Matrix (Fin N) (Fin v.card) ℝ := fun i r => (e r).val i
  let A : Matrix (Fin v.card) (Fin N) ℝ := fun r j => w j (e r).val
  have heE (r : Fin v.card) : (e r).val ∈ E := by
    exact hf.mem_toFinset.mp (e r).property
  have hV : EntrywiseNonnegative V := by
    intro i r
    exact nonnegative_of_mem_columnHull U hU.1 (e r).val (heE r).1.1 i
  have hA : EntrywiseNonnegative A := by
    intro r j
    exact hw0 j (e r).val (e r).property
  have hVA : V * A = X := by
    ext i j
    change (∑ r : Fin v.card, (e r).val i * w j (e r).val) = X i j
    calc
      (∑ r : Fin v.card, (e r).val i * w j (e r).val) =
          ∑ a : v, a.val i * w j a.val := e.sum_comp (fun a : v => a.val i * w j a.val)
      _ = ∑ a ∈ v, a i * w j a := Finset.sum_coe_sort v (fun a : Fin N → ℝ => a i * w j a)
      _ = X i j := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
          congrFun (hwx j) i
  have hplane (r : Fin v.card) : (fun i => V i r) ∈ columnAffineSpan X :=
    (heE r).1.2
  have hcount : N ≤ v.card :=
    factor_width_ge_order_of_column_plane X V A hX hrX hdiag hoff hV hA hVA hplane
  change N ≤ E.ncard
  rw [Set.ncard_eq_toFinset_card E hf]
  exact hcount

#print axioms nonnegative_of_mem_columnHull
#print axioms finite_extremePoints_columnSection
#print axioms convexHull_extremePoints_columnSection
#print axioms section_contact_bound

end NLA.NR04
