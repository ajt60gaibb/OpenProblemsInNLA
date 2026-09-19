/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual affine dimension in Matthew J. Colbrook's NR-04 proof, University
of Cambridge. Statements were recorded before proof bodies. This author
does not count as an independent final referee for NR-04. No C08 statement
is changed and no planar order or vertex bound is assumed.
-/
import NLA.NR04.SmallSectionRankThree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.NR04

/-- The genuine coordinate-sum functional on the ambient vector space. -/
def coordinateSum (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' u v := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

/-- Normalization identifies the actual affine direction with the zero-sum
part of the actual column span. The selected column supplies nonemptiness. -/
lemma column_direction_mem_iff {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (j0 : Fin N) (v : Fin N → ℝ) :
    v ∈ (columnAffineSpan X).direction ↔
      v ∈ Submodule.span ℝ (Set.range X.col) ∧ ∑ i, v i = 0 := by
  have hp : X.col j0 ∈ columnAffineSpan X := by
    change X.col j0 ∈ affineSpan ℝ (Set.range X.col)
    exact mem_affineSpan ℝ (Set.mem_range_self j0)
  have hpW : X.col j0 ∈ Submodule.span ℝ (Set.range X.col) :=
    Submodule.subset_span (Set.mem_range_self j0)
  have hpsum : (∑ i, X.col j0 i) = 1 := hX.2 j0
  constructor
  · intro hv
    obtain ⟨p, hpA, heq⟩ :=
      (AffineSubspace.mem_direction_iff_eq_vsub_right hp v).mp hv
    change v = p - X.col j0 at heq
    have hpSum := sum_eq_one_of_mem_columnAffineSpan X hX p hpA
    have hpSpan : p ∈ Submodule.span ℝ (Set.range X.col) :=
      affineSpan_subset_span (k := ℝ) hpA
    rw [heq]
    refine ⟨(Submodule.span ℝ (Set.range X.col)).sub_mem hpSpan hpW, ?_⟩
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hpSum, hpsum, sub_self]
  · rintro ⟨hvW, hvsum⟩
    have hq : v + X.col j0 ∈ columnAffineSpan X := by
      apply mem_columnAffineSpan_of_mem_span_sum_one X hX
      · exact (Submodule.span ℝ (Set.range X.col)).add_mem hvW hpW
      · simp only [Pi.add_apply, Finset.sum_add_distrib, hvsum, hpsum, zero_add]
    have hd := AffineSubspace.vsub_mem_direction hq hp
    change v + X.col j0 - X.col j0 ∈ (columnAffineSpan X).direction at hd
    simpa only [add_sub_cancel_right] using hd

/-- The affine plane dimension is derived from ordinary rank and column
normalization, including the argument that the index type is nonempty. -/
theorem column_affine_direction_finrank {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) :
    Module.finrank ℝ (columnAffineSpan X).direction = 2 := by
  have hN : 0 < N := by
    have hle := Matrix.rank_le_width X
    rw [hrX] at hle
    omega
  let j0 : Fin N := ⟨0, hN⟩
  let W : Submodule ℝ (Fin N → ℝ) := Submodule.span ℝ (Set.range X.col)
  let V : Submodule ℝ (Fin N → ℝ) := (columnAffineSpan X).direction
  let f : W →ₗ[ℝ] ℝ := (coordinateSum N).comp W.subtype
  have hWdim : Module.finrank ℝ W = 3 :=
    (Matrix.rank_eq_finrank_span_cols X).symm.trans hrX
  have hdir (v : Fin N → ℝ) :
      v ∈ V ↔ v ∈ W ∧ ∑ i, v i = 0 := column_direction_mem_iff X hX j0 v
  have hfSurj : Function.Surjective f := by
    intro r
    have hpW : X.col j0 ∈ W := Submodule.subset_span (Set.mem_range_self j0)
    refine ⟨r • (⟨X.col j0, hpW⟩ : W), ?_⟩
    change coordinateSum N (r • X.col j0) = r
    rw [map_smul]
    change r * (∑ i, X.col j0 i) = r
    change r * (∑ i, X i j0) = r
    rw [hX.2 j0, mul_one]
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hfSurj
  have hker : Module.finrank ℝ f.ker = 2 := by
    have hdim := f.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, CommSemiring.finrank_self, hWdim] at hdim
    omega
  let e : V ≃ₗ[ℝ] f.ker :=
    { toFun := fun v => by
        have hv := (hdir v.1).mp v.2
        refine ⟨⟨v.1, hv.1⟩, ?_⟩
        change (∑ i, v.1 i) = 0
        exact hv.2
      invFun := fun v => by
        refine ⟨v.1.1, (hdir v.1.1).mpr ⟨v.1.2, ?_⟩⟩
        have hv := v.2
        change (∑ i, v.1.1 i) = 0 at hv
        exact hv
      left_inv := by intro v; apply Subtype.ext; rfl
      right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl
      map_add' := by intro u v; apply Subtype.ext; apply Subtype.ext; rfl
      map_smul' := by intro r v; apply Subtype.ext; apply Subtype.ext; rfl }
  exact e.finrank_eq.trans hker

#print axioms column_direction_mem_iff
#print axioms column_affine_direction_finrank
#assert_trust kernel column_direction_mem_iff
#assert_trust kernel column_affine_direction_finrank

end NLA.NR04
