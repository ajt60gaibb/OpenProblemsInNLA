/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual affine-plane bridge for Matthew J. Colbrook's NR-04 argument,
University of Cambridge. The column plane is derived from original rank
and normalization; no dimension or geometric conclusion is supplied.
-/
import NLA.NR04.NineGridPlanarObstruction
import NLA.NR04.AffinePlaneCoordinates

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

theorem nine_grid_in_column_plane_not_all_extreme {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X) (hrX : X.rank = 3)
    (w : Fin 3 × Fin 3 → Fin N → ℝ) (hw : Function.Injective w)
    (hmem : ∀ a, w a ∈ columnAffineSpan X)
    (hcross : ∀ i k j l : Fin 3, i < k → j < l →
      (openSegment ℝ (w (i, j)) (w (k, l)) ∩
        openSegment ℝ (w (i, l)) (w (k, j))).Nonempty) :
    ¬ (∀ a, w a ∈ (convexHull ℝ (Set.range w)).extremePoints ℝ) := by
  classical
  intro hext
  obtain ⟨g, hginj, hgrange⟩ := column_affine_plane_parametrization X hX hrX
  have hpre : ∀ a, ∃ z, g z = w a := by
    intro a
    have hwa : w a ∈ Set.range g := by rw [hgrange]; exact hmem a
    exact hwa
  choose z hz using hpre
  have hzinj : Function.Injective z := by
    intro a b hab
    apply hw
    calc
      w a = g (z a) := (hz a).symm
      _ = g (z b) := congrArg g hab
      _ = w b := hz b
  have hzr : g '' Set.range z = Set.range w := by
    ext y
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (hz a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨z a, Set.mem_range_self a, hz a⟩
  have hhull : g '' convexHull ℝ (Set.range z) = convexHull ℝ (Set.range w) := by
    rw [g.image_convexHull, hzr]
  have hextz : ∀ a, z a ∈ (convexHull ℝ (Set.range z)).extremePoints ℝ := by
    intro a
    apply (affine_injective_extreme_image_iff g hginj
      (convexHull ℝ (Set.range z)) (z a)).mp
    rw [hhull, hz a]
    exact hext a
  have hcrossz : ∀ i k j l : Fin 3, i < k → j < l →
      (openSegment ℝ (z (i, j)) (z (k, l)) ∩
        openSegment ℝ (z (i, l)) (z (k, j))).Nonempty := by
    intro i k j l hik hjl
    apply (affine_injective_open_crossing_iff g hginj
      (z (i, j)) (z (k, l)) (z (i, l)) (z (k, j))).mpr
    simpa only [hz] using hcross i k j l hik hjl
  exact nine_grid_not_all_extreme z hzinj hcrossz hextz

#print axioms nine_grid_in_column_plane_not_all_extreme
#assert_trust kernel nine_grid_in_column_plane_not_all_extreme

end NLA.NR04
