import NLA.Proofs.TR06.ControlledProjectionAtlas
import NLA.TR06.FiniteVolume

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology Function
open MeasureTheory Set Function
namespace NLA.Proofs.TR06
open NLA.TR06.Area NLA.TR06.Area.Proposed

/-- A bounded genuine smooth graph has finite intrinsic Hausdorff volume once
its controlled coordinate-projection fibers have uniform finite-subset bounds. -/
theorem finite_volume_of_controlled_projection_fibers {m N : ℕ} {S : Set (Euclid N)}
    (hm : m ≤ N) (hS : HasSmoothEmbeddedCharts m S) (hbounded : Bornology.IsBounded S)
    (hbound : ∀ K : ℝ≥0, ∀ σ : Fin m ↪ Fin N, ∃ B : ℕ,
      ∀ x (q : Finset (Euclid N)),
        (↑q : Set (Euclid N)) ⊆ {z | z ∈ ControlledProjectionSet K S σ ∧
          coordProjection σ z = x} → q.card ≤ B) :
    (μHE[m] : Measure (Euclid N)) S < ⊤ := by
  classical
  obtain ⟨K,t,f,_hK,ht,hLip,hπ,hctl,hdisj,hcover⟩ :=
    uniform_controlled_projection_atlas m N S hm hS
  have hfinite (σ : Fin m ↪ Fin N) :
      (μHE[m] : Measure (Euclid N)) (⋃ j, f σ j '' t σ j) < ⊤ := by
    obtain ⟨B,hB⟩ := hbound K σ
    have hdisj' : Pairwise (Disjoint on fun j => f σ j '' t σ j) := by
      intro i j hij
      exact hdisj (show (σ,i) ≠ (σ,j) from fun h => hij (congrArg Prod.snd h))
    have hover := bounded_overlap_of_fiber_bound (hπ σ) hdisj' (hctl σ) hB
    let V := coordProjection σ '' S
    have hV : ∀ j, t σ j ⊆ V := by
      intro j x hx
      refine ⟨f σ j x,?_,hπ σ j x hx⟩
      obtain ⟨b,u,hu,hbu,_⟩ := hctl σ j ⟨x,hx,rfl⟩
      rw [← hbu]
      exact (b u).property
    have hVfinite : volume V < ⊤ := by
      apply Bornology.IsBounded.measure_lt_top
      exact (coordProjectionL σ).lipschitz.isBounded_image hbounded
    simpa only [finrank_euclideanSpace_fin] using
      (finite_volume_of_bounded_overlap hVfinite (ht σ) hV (hLip σ) hover).2
  rw [hcover]
  apply lt_of_le_of_lt (measure_iUnion_le _) ?_
  simpa only [tsum_fintype] using ENNReal.sum_lt_top.mpr (fun σ _ => hfinite σ)

#assert_trust kernel finite_volume_of_controlled_projection_fibers
#print axioms finite_volume_of_controlled_projection_fibers
end NLA.Proofs.TR06
