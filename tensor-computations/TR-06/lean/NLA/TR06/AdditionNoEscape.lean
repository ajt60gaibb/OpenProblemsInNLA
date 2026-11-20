/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.RegularChartDefinitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace NLA.TR06.Proposed

theorem addition_fiber_neighborhood : AdditionFiberNeighborhoodStatement := by
  classical
  intro d n r U hU hproper A hAU hArank V hV hfiber
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hAU)
  let K := Metric.closedBall A (δ / 2)
  have hKU : K ⊆ U := by
    intro B hB
    apply hδU
    exact lt_of_le_of_lt (show dist B A ≤ δ / 2 from hB) (by linarith)
  let T := {a : Fin r → Tensor ℝ d n |
      a ∈ closedRankOneProduct ℝ d n r ∧ (∑ i, a i) ∈ K}
  have hT : IsCompact T := hproper K (isCompact_closedBall _ _) hKU
  let f : (Fin r → Tensor ℝ d n) → Tensor ℝ d n := fun a => ∑ i, a i
  have hf : Continuous f := continuous_finsetSum _ (fun i _ => continuous_apply i)
  have himage : IsClosed (f '' (T \ W)) := (hT.diff hW).image hf |>.isClosed
  have hnot : A ∉ f '' (T \ W) := by
    rintro ⟨a, ha, hsum⟩
    have hmem : a ∈ closedAdditionFiber r A := ⟨ha.1.1, hsum⟩
    let a' : OrderedRankOne d n r := ⟨a, rankOne_of_mem_closedAdditionFiber hArank hmem⟩
    have haV := hfiber a' hsum
    have haW : a ∈ W := by
      change a' ∈ Subtype.val ⁻¹' W
      rw [hWV]
      exact haV
    exact ha.2 haW
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (himage.isOpen_compl.mem_nhds hnot)
  refine ⟨min ε (δ / 2), lt_min hε (by linarith), ?_⟩
  intro a ha
  have haW : a.val ∈ W := by
    by_contra houtside
    have haT : a.val ∈ T := by
      exact ⟨fun i => Or.inr (a.property i), le_of_lt (lt_of_lt_of_le ha (min_le_right _ _))⟩
    have hsumout := hεball (lt_of_lt_of_le ha (min_le_left _ _))
    exact hsumout ⟨a.val, ⟨haT, houtside⟩, rfl⟩
  rw [← hWV]
  exact haW

#print axioms addition_fiber_neighborhood
#assert_trust kernel addition_fiber_neighborhood
end NLA.TR06.Proposed
