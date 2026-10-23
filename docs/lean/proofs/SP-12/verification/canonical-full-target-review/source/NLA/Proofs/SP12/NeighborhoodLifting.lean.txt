import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic
import LeanCert.Tactic.Verification

/-! A neighborhood image provides an actual small nonzero parameter and a
preimage inside the chosen good neighborhood. No continuous choice is needed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter Set
open scoped Topology

namespace NLA.Proofs.SP12

theorem exists_nonzero_lift_in_nhds {E F B : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [Zero F] [Zero B]
    (f : E → F) (a : E) (hmap : map f (𝓝 a) = 𝓝 (0 : F))
    (U : Set (E × B)) (hU : U ∈ 𝓝 (a, (0 : B)))
    (target : ℝ → F × B) (ht : Tendsto target (𝓝 0) (𝓝 (0, 0))) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∃ p ∈ U, (f p.1, p.2) = target ε := by
  let H : E × B → F × B := fun p => (f p.1, p.2)
  have hm : map H (𝓝 (a, (0 : B))) = 𝓝 ((0 : F), (0 : B)) := by
    have heq := (prod_map_map_eq (f₁ := 𝓝 a) (f₂ := 𝓝 (0 : B))
      (m₁ := f) (m₂ := id)).symm
    have heq' : map H (𝓝 a ×ˢ 𝓝 (0 : B)) = map f (𝓝 a) ×ˢ 𝓝 (0 : B) := by
      simpa only [H, map_id, id_eq] using heq
    rw [nhds_prod_eq, heq', hmap, nhds_prod_eq]
  have hi : H '' U ∈ 𝓝 ((0 : F), (0 : B)) := by
    rw [← hm]
    exact image_mem_map hU
  have he : {ε : ℝ | target ε ∈ H '' U} ∈ 𝓝 0 := ht hi
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp he
  have hhalf : (δ / 2 : ℝ) ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  obtain ⟨p, hp, heq⟩ := hb hhalf
  exact ⟨δ / 2, ne_of_gt (half_pos hδ), p, hp, heq⟩

#assert_trust kernel exists_nonzero_lift_in_nhds
#print axioms exists_nonzero_lift_in_nhds

end NLA.Proofs.SP12
