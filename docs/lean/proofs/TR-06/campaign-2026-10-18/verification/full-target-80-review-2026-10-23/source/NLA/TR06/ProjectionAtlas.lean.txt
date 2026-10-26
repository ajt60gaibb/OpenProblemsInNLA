/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.

This proves exactly the independently reviewed boundary C. Uniform algebraic
or semialgebraic fiber bounds remain a separate, unproved obligation D.
-/
import NLA.TR06.ProjectionLocal
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
open MeasureTheory Set Function Metric Module Filter

namespace NLA.TR06.Area.Proposed

/-- In dimension zero the chart hypothesis really gives a discrete, countable set.
This records the degenerate case explicitly; the atlas construction below also
works uniformly in dimension zero. -/
theorem zero_dimensional_charts_countable {N : ℕ} {S : Set (Euclid N)}
    (hS : HasSmoothEmbeddedCharts 0 S) : S.Countable := by
  have hdiscrete : DiscreteTopology S := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro z
    obtain ⟨c, hz, -, -⟩ := hS z
    have htarget : c.target = {z} := by
      apply subset_antisymm
      · intro w hw
        exact mem_singleton_iff.mpr
          (c.symm.injOn hw hz (Subsingleton.elim _ _))
      · exact singleton_subset_iff.mpr hz
    rw [← htarget]
    exact c.open_target
  let := hdiscrete
  exact Countable.to_set (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- The uniform coordinate projection atlas, with no finiteness-of-volume or
semialgebraic hypotheses. Empty sets and zero-dimensional charts are included. -/
theorem uniform_projection_atlas : UniformProjectionAtlasStatement := by
  classical
  intro m N S _hm hS
  by_cases hne : S = ∅
  · subst S
    refine ⟨1, fun _ _ => ∅, fun _ _ _ => 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ => MeasurableSet.empty
    · exact fun _ _ x hx => hx.elim
    · simp
    · simp
    · intro a b hab; simp
    · simp
  obtain ⟨K, hK, hlocal⟩ := local_projection_charts m N
  choose σ c hmem hLip hπ using hlocal S hS
  obtain ⟨q, hqcount, hqcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun z : S => (c z).target) (fun z => (c z).open_target) (by
      intro z _
      exact mem_iUnion.mpr ⟨z, hmem z⟩)
  obtain ⟨z0, hz0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hqne : q.Nonempty := by
    obtain ⟨z, hz, -⟩ := mem_iUnion₂.mp (hqcover (show (⟨z0, hz0⟩ : S) ∈ Set.univ from mem_univ _))
    exact ⟨z, hz⟩
  obtain ⟨e, he⟩ := hqcount.exists_surjective hqne
  let C : ℕ → OpenPartialHomeomorph (Euclid m) S := fun j => c (e j).val
  let p : ℕ → (Fin m ↪ Fin N) := fun j => σ (e j).val
  let g : ℕ → Euclid m → Euclid N := fun j x => (C j x).val
  have hcover : ∀ z : S, ∃ j, z ∈ (C j).target := by
    intro z
    obtain ⟨w, hwq, hw⟩ := mem_iUnion₂.mp (hqcover (mem_univ z))
    obtain ⟨j, hj⟩ := he ⟨w, hwq⟩
    refine ⟨j, ?_⟩
    simpa only [C, hj] using hw
  let W : ℕ → Set (Euclid N) := fun j => g j '' (C j).source
  have hWmeas (j : ℕ) : MeasurableSet (W j) := by
    apply (C j).open_source.measurableSet.image_of_continuousOn_injOn
      (hLip (e j).val).continuousOn
    intro x hx y hy hxy
    exact (C j).injOn hx hy (Subtype.ext hxy)
  have hWcover : S = ⋃ j, W j := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨j, hj⟩ := hcover ⟨z, hz⟩
      exact mem_iUnion.mpr ⟨j, (C j).symm ⟨z, hz⟩,
        (C j).symm.map_source hj, congrArg Subtype.val ((C j).right_inv hj)⟩
    · intro z hz
      obtain ⟨j, x, -, rfl⟩ := mem_iUnion.mp hz
      exact (C j x).property
  let P := disjointed W
  have hPmeas (j : ℕ) : MeasurableSet (P j) := MeasurableSet.disjointed hWmeas j
  have hPsub (j : ℕ) : P j ⊆ W j := disjointed_subset W j
  have hPcover : S = ⋃ j, P j := by rw [iUnion_disjointed]; exact hWcover
  have hπ' (j : ℕ) : ∀ x ∈ (C j).source, coordProjection (p j) (g j x) = x :=
    hπ (e j).val
  have hπinj (j : ℕ) : Set.InjOn (coordProjection (p j)) (W j) := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have huv : u = v := by rwa [hπ' j u hu, hπ' j v hv] at hxy
    exact congrArg (g j) huv
  let t : ℕ → Set (Euclid m) := fun j => coordProjection (p j) '' P j
  have htmeas (j : ℕ) : MeasurableSet (t j) :=
    (hPmeas j).image_of_continuousOn_injOn (coordProjectionL (p j)).continuous.continuousOn
      ((hπinj j).mono (hPsub j))
  have htsub (j : ℕ) : t j ⊆ (C j).source := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨u, hu, rfl⟩ := hPsub j hy
    rwa [hπ' j u hu]
  have himage (j : ℕ) : g j '' t j = P j := by
    apply subset_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, hu, rfl⟩ := hPsub j hz
      simpa only [hπ' j u hu] using hz
    · intro y hy
      obtain ⟨u, hu, hgu⟩ := hPsub j hy
      refine ⟨u, ⟨y, hy, ?_⟩, hgu⟩
      rw [← hgu, hπ' j u hu]
  have hloc (j : ℕ) : g j '' t j ⊆ ProjectionLocallyInjectiveSet S (p j) :=
    (Set.image_mono (htsub j)).trans
      (projection_chart_locally_injective (p j) (C j) (hπ' j))
  let T : (Fin m ↪ Fin N) → ℕ → Set (Euclid m) :=
    fun σ j => if p j = σ then t j else ∅
  have hgroup (σ : Fin m ↪ Fin N) (j : ℕ) :
      g j '' T σ j = if p j = σ then P j else ∅ := by
    dsimp [T]
    split_ifs <;> simp only [himage, image_empty]
  refine ⟨K, T, fun _ j => g j, hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ j
    dsimp [T]
    split_ifs
    · exact htmeas j
    · exact MeasurableSet.empty
  · intro σ j
    apply (hLip (e j).val).mono
    dsimp [T]
    split_ifs
    · exact htsub j
    · exact empty_subset _
  · intro σ j x hx
    dsimp [T] at hx
    split_ifs at hx with h
    · subst σ
      exact hπ' j x (htsub j hx)
    · exact hx.elim
  · intro σ j
    dsimp [T]
    split_ifs with h
    · subst σ
      exact hloc j
    · simp
  · intro a b hab
    change Disjoint (g a.2 '' T a.1 a.2) (g b.2 '' T b.1 b.2)
    rw [hgroup, hgroup]
    split_ifs with ha hb
    · apply disjoint_disjointed W
      intro hj
      apply hab
      apply Prod.ext
      · rw [hj] at ha
        exact ha.symm.trans hb
      · exact hj
    · simp
    · simp
    · simp
  · rw [hPcover]
    ext y
    simp only [mem_iUnion, hgroup]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨p j, j, by simpa using hj⟩
    · rintro ⟨σ, j, hj⟩
      split_ifs at hj with h
      · exact ⟨j, hj⟩
      · exact hj.elim

#print axioms zero_dimensional_charts_countable
#print axioms uniform_projection_atlas
#assert_trust kernel zero_dimensional_charts_countable
#assert_trust kernel uniform_projection_atlas

end NLA.TR06.Area.Proposed
