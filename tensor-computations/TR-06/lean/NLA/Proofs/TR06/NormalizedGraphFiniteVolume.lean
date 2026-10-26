import NLA.Proofs.TR06.NormalizedGraphFiniteFibers
import NLA.Proofs.TR06.NormalizedGraphBounded
import NLA.Proofs.TR06.ControlledProjectionVolume

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
namespace NLA.Proofs.TR06
open Set MeasureTheory NLA.TR06 NLA.TR06.Area.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- The complete actual normalized annular graph, with all ordered branches,
has finite expected-dimensional Euclidean Hausdorff volume. -/
theorem normalizedAnnularGraph_volume_lt_top (hd : 0 < d) :
    (μHE[expectedDimension d n r] : Measure (NormalizedGraphAmbient d n r))
      (normalizedAnnularGraph d n r) < ⊤ := by
  classical
  let S := euclideanNormalizedGraph d n r
  have hcharts := euclideanNormalizedGraph_hasSmoothEmbeddedCharts (n := n) (r := r) hd
  have hfinite : (μHE[expectedDimension d n r] : Measure (Euclid (graphAmbientDimension d n r))) S < ⊤ := by
    by_cases hS : S = ∅
    · simp [hS]
    obtain ⟨z,hz⟩ := Set.nonempty_iff_ne_empty.mpr hS
    obtain ⟨c,hct,_hcsm,hcinj⟩ := hcharts ⟨z,hz⟩
    have hdim := LinearMap.finrank_le_finrank_of_injective
      (hcinj (c.symm ⟨z,hz⟩) (c.symm.map_source hct))
    simp only [finrank_euclideanSpace_fin] at hdim
    exact finite_volume_of_controlled_projection_fibers hdim hcharts
      euclideanNormalizedGraph_bounded (fun K σ => normalizedGraph_controlled_finite_subset_bound hd K σ)
  have heq := (graphEuclideanEquiv d n r).isometry.euclideanHausdorffMeasure_image
    (d := expectedDimension d n r) (normalizedAnnularGraph d n r)
  change (μHE[expectedDimension d n r] : Measure (Euclid (graphAmbientDimension d n r))) S =
    (μHE[expectedDimension d n r] : Measure (NormalizedGraphAmbient d n r))
      (normalizedAnnularGraph d n r) at heq
  rwa [heq] at hfinite

#assert_trust kernel normalizedAnnularGraph_volume_lt_top
#print axioms normalizedAnnularGraph_volume_lt_top
end NLA.Proofs.TR06
