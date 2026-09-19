/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Exact affine-plane coordinates for Matthew J. Colbrook's NR-04 proof,
University of Cambridge. Actual convex hulls, extreme points, and open
segments are transported by an injective affine parametrization. No
cyclic order or section vertex bound is supplied as a premise.
-/
import NLA.NR04.AffinePlaneDimension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.NR04

/-- A normalized rank-three column family spans an actual affine copy of R².
The embedding is injective and its range is exactly the original affine span. -/
theorem column_affine_plane_parametrization {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) :
    ∃ g : (Fin 2 → ℝ) →ᵃ[ℝ] (Fin N → ℝ),
      Function.Injective g ∧ Set.range g = (columnAffineSpan X : Set (Fin N → ℝ)) := by
  have hN : 0 < N := by
    have hle := Matrix.rank_le_width X
    rw [hrX] at hle
    omega
  let j0 : Fin N := ⟨0, hN⟩
  let A : AffineSubspace ℝ (Fin N → ℝ) := columnAffineSpan X
  have hp : X.col j0 ∈ A := by
    change X.col j0 ∈ affineSpan ℝ (Set.range X.col)
    exact mem_affineSpan ℝ (Set.mem_range_self j0)
  let p0 : A := ⟨X.col j0, hp⟩
  letI : Nonempty A := ⟨p0⟩
  have hdim : Module.finrank ℝ A.direction = 2 :=
    column_affine_direction_finrank X hX hrX
  let b := Module.finBasisOfFinrankEq ℝ A.direction hdim
  let e : A ≃ᵃ[ℝ] (Fin 2 → ℝ) :=
    (AffineEquiv.vaddConst ℝ p0).symm.trans b.equivFun.toAffineEquiv
  let g : (Fin 2 → ℝ) →ᵃ[ℝ] (Fin N → ℝ) :=
    A.subtype.comp e.symm.toAffineMap
  refine ⟨g, ?_, ?_⟩
  · intro u v h
    apply e.symm.injective
    apply Subtype.coe_injective
    exact h
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (e.symm z).2
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      change ((e.symm (e ⟨y, hy⟩) : A) : Fin N → ℝ) = y
      rw [e.symm_apply_apply]

/-- Injective affine maps preserve and reflect actual extreme points. -/
lemma affine_injective_extreme_image_iff {m n : ℕ}
    (f : (Fin m → ℝ) →ᵃ[ℝ] (Fin n → ℝ)) (hf : Function.Injective f)
    (S : Set (Fin m → ℝ)) (x : Fin m → ℝ) :
    f x ∈ (f '' S).extremePoints ℝ ↔ x ∈ S.extremePoints ℝ := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy, heq⟩ := hx.1
      have hyx : y = x := hf heq
      simpa only [hyx] using hy
    · intro y hy z hz hseg
      apply hf
      apply hx.2 ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
      rw [← image_openSegment ℝ f y z]
      exact ⟨x, hseg, rfl⟩
  · intro hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro y ⟨a, ha, rfl⟩ z ⟨b, hb, rfl⟩ hseg
    rw [← image_openSegment ℝ f a b] at hseg
    obtain ⟨c, hc, heq⟩ := hseg
    have hcx : c = x := hf heq
    subst c
    exact congrArg f (hx.2 ha hb hc)

/-- No open-diagonal intersection is created or lost by an injective affine map. -/
lemma affine_injective_open_crossing_iff {m n : ℕ}
    (f : (Fin m → ℝ) →ᵃ[ℝ] (Fin n → ℝ)) (hf : Function.Injective f)
    (a b c d : Fin m → ℝ) :
    (openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty ↔
      (openSegment ℝ (f a) (f b) ∩ openSegment ℝ (f c) (f d)).Nonempty := by
  constructor
  · rintro ⟨p, hp, hq⟩
    refine ⟨f p, ?_, ?_⟩
    · rw [← image_openSegment ℝ f a b]
      exact ⟨p, hp, rfl⟩
    · rw [← image_openSegment ℝ f c d]
      exact ⟨p, hq, rfl⟩
  · rintro ⟨y, hy, hz⟩
    rw [← image_openSegment ℝ f a b] at hy
    rw [← image_openSegment ℝ f c d] at hz
    obtain ⟨p, hp, hpy⟩ := hy
    obtain ⟨q, hq, hqy⟩ := hz
    have hpq : p = q := hf (hpy.trans hqy.symm)
    exact ⟨p, hp, by simpa only [hpq] using hq⟩

/-- Coordinate representatives retain the actual family, its full convex hull,
every extreme-point predicate, and all open-diagonal intersections. -/
theorem column_family_plane_coordinates {N m : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) (w : Fin m → Fin N → ℝ)
    (hw : ∀ i, w i ∈ columnAffineSpan X) :
    ∃ z : Fin m → Fin 2 → ℝ,
    ∃ g : (Fin 2 → ℝ) →ᵃ[ℝ] (Fin N → ℝ),
      Function.Injective g ∧
      (∀ i, g (z i) = w i) ∧
      g '' convexHull ℝ (Set.range z) = convexHull ℝ (Set.range w) ∧
      (∀ i, z i ∈ (convexHull ℝ (Set.range z)).extremePoints ℝ ↔
        w i ∈ (convexHull ℝ (Set.range w)).extremePoints ℝ) ∧
      (Function.Injective w → Function.Injective z) ∧
      (∀ i j k l,
        (openSegment ℝ (z i) (z j) ∩ openSegment ℝ (z k) (z l)).Nonempty ↔
        (openSegment ℝ (w i) (w j) ∩ openSegment ℝ (w k) (w l)).Nonempty) := by
  classical
  obtain ⟨g, hginj, hgrange⟩ := column_affine_plane_parametrization X hX hrX
  have hpre : ∀ i, ∃ z, g z = w i := by
    intro i
    have hmem : w i ∈ Set.range g := by rw [hgrange]; exact hw i
    exact hmem
  choose z hz using hpre
  have hzr : g '' Set.range z = Set.range w := by
    ext y
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hz i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, hz i⟩
  have hhull : g '' convexHull ℝ (Set.range z) = convexHull ℝ (Set.range w) := by
    rw [g.image_convexHull, hzr]
  refine ⟨z, g, hginj, hz, hhull, ?_, ?_, ?_⟩
  · intro i
    have he := affine_injective_extreme_image_iff g hginj
      (convexHull ℝ (Set.range z)) (z i)
    rw [hhull, hz i] at he
    exact he.symm
  · intro hwinj i j hij
    apply hwinj
    calc
      w i = g (z i) := (hz i).symm
      _ = g (z j) := congrArg g hij
      _ = w j := hz j
  · intro i j k l
    simpa only [hz] using affine_injective_open_crossing_iff g hginj
      (z i) (z j) (z k) (z l)

#print axioms column_affine_plane_parametrization
#print axioms affine_injective_extreme_image_iff
#print axioms affine_injective_open_crossing_iff
#print axioms column_family_plane_coordinates
#assert_trust kernel column_affine_plane_parametrization
#assert_trust kernel affine_injective_extreme_image_iff
#assert_trust kernel affine_injective_open_crossing_iff
#assert_trust kernel column_family_plane_coordinates

end NLA.NR04
