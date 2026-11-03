/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.ProjectionTangent

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
open MeasureTheory Set Function Metric Module Filter

namespace NLA.TR06.Area.Proposed

/-- A right-inverse projection chart is locally injective on the entire set S,
since its target is open in S. No restriction to a chosen sheet is substituted. -/
theorem projection_chart_locally_injective {m N : ℕ} {S : Set (Euclid N)}
    (σ : Fin m ↪ Fin N) (b : OpenPartialHomeomorph (Euclid m) S)
    (hπ : ∀ x ∈ b.source, coordProjection σ (b x).val = x) :
    (fun x => (b x).val) '' b.source ⊆ ProjectionLocallyInjectiveSet S σ := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hb : b x ∈ b.target := b.map_source hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp b.open_target (b x) hb
  refine ⟨(b x).property, ε, hε, ?_⟩
  intro y hy w hw heq
  have hyb : (⟨y, hy.1⟩ : S) ∈ b.target := hball hy.2
  have hwb : (⟨w, hw.1⟩ : S) ∈ b.target := hball hw.2
  have hyp : coordProjection σ y = b.symm ⟨y, hy.1⟩ := by
    simpa only [b.right_inv hyb] using hπ (b.symm ⟨y, hy.1⟩) (b.symm.map_source hyb)
  have hwp : coordProjection σ w = b.symm ⟨w, hw.1⟩ := by
    simpa only [b.right_inv hwb] using hπ (b.symm ⟨w, hw.1⟩) (b.symm.map_source hwb)
  have hs : (⟨y, hy.1⟩ : S) = ⟨w, hw.1⟩ :=
    b.symm.injOn hyb hwb (by rwa [← hyp, ← hwp])
  exact congrArg Subtype.val hs

/-- Every smooth embedded chart can locally be replaced by a coordinate-projection
inverse chart with the common dimension-dependent Lipschitz bound. -/
theorem local_projection_charts (m N : ℕ) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (S : Set (Euclid N)), HasSmoothEmbeddedCharts m S →
      ∀ z : S, ∃ (σ : Fin m ↪ Fin N) (b : OpenPartialHomeomorph (Euclid m) S),
        z ∈ b.target ∧ LipschitzOnWith K (fun x => (b x).val) b.source ∧
        (∀ x ∈ b.source, coordProjection σ (b x).val = x) := by
  classical
  obtain ⟨K, hK, hbound⟩ := uniform_tangent_coordinate_bound m N
  refine ⟨2 * K, by positivity, ?_⟩
  intro S hS z
  obtain ⟨c, hzc, hcsmooth, hcinj⟩ := hS z
  let u := c.symm z
  have hu : u ∈ c.source := c.symm.map_source hzc
  let g : Euclid m → Euclid N := fun v => (c v).val
  let A := fderiv ℝ g u
  have hA : Injective A := hcinj u hu
  have hg : HasStrictFDerivAt g A u :=
    (hcsmooth.contDiffAt (c.open_source.mem_nhds hu)).hasStrictFDerivAt one_ne_zero
  obtain ⟨σ, hσ⟩ := hbound A hA
  obtain ⟨e, he, hnorm⟩ := tangent_coordinate_equiv A hA σ hσ
  let q : Euclid m → Euclid m := fun v => coordProjectionL σ (g v)
  have hq : HasStrictFDerivAt q (e : Euclid m →L[ℝ] Euclid m) u := by
    rw [he]
    exact (coordProjectionL σ).hasStrictFDerivAt.comp u hg
  let l := hq.toOpenPartialHomeomorph q
  let b := l.symm.trans c
  let y := q u
  have hul : u ∈ l.source := hq.mem_toOpenPartialHomeomorph_source
  have hyl : y ∈ l.target := l.map_source hul
  have hyu : l.symm y = u := l.left_inv hul
  have hzb : z ∈ b.target := by
    change z ∈ c.target ∩ c.symm ⁻¹' l.source
    exact ⟨hzc, hul⟩
  have hbzy : b.symm z = y := rfl
  have hinv : HasStrictFDerivAt l.symm
      (e.symm : Euclid m →L[ℝ] Euclid m) y := hq.to_localInverse
  have hg' : HasStrictFDerivAt g A (l.symm y) := by rwa [hyu]
  have hb : HasStrictFDerivAt (fun v => (b v).val)
      (A.comp (e.symm : Euclid m →L[ℝ] Euclid m)) y := hg'.comp y hinv
  have hnorm' : ‖A.comp (e.symm : Euclid m →L[ℝ] Euclid m)‖₊ < 2 * K := by
    have H : ‖A.comp (e.symm : Euclid m →L[ℝ] Euclid m)‖₊ ≤ K := hnorm
    exact H.trans_lt (by simpa only [two_mul] using lt_add_of_pos_right K hK)
  obtain ⟨U, hU, hLip⟩ := hb.exists_lipschitzOnWith_of_nnnorm_lt (2 * K) hnorm'
  refine ⟨σ, b.restr U, ?_, ?_, ?_⟩
  · rw [b.restr_target]
    exact ⟨hzb, by rw [mem_preimage, hbzy]; exact mem_interior_iff_mem_nhds.mpr hU⟩
  · exact hLip.mono (fun x hx => interior_subset hx.2)
  · intro x hx
    have hxb : x ∈ b.source := hx.1
    have hxl : x ∈ l.target := hxb.1
    change l (l.symm x) = x
    exact l.right_inv hxl

#print axioms projection_chart_locally_injective
#print axioms local_projection_charts
#assert_trust kernel projection_chart_locally_injective
#assert_trust kernel local_projection_charts

end NLA.TR06.Area.Proposed
