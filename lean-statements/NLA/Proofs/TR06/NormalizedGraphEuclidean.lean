import NLA.Proofs.TR06.NormalizedGraphCharts
import NLA.Proofs.TR06.ControlledProjectionAtlas

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology
namespace NLA.Proofs.TR06
open Set NLA.TR06 NLA.TR06.Area.Proposed

abbrev graphAmbientDimension (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  Module.finrank ℝ (NormalizedGraphAmbient d n r)

def graphEuclideanEquiv (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    NormalizedGraphAmbient d n r ≃ₗᵢ[ℝ] Euclid (graphAmbientDimension d n r) :=
  (stdOrthonormalBasis ℝ (NormalizedGraphAmbient d n r)).repr

def euclideanNormalizedGraph (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Set (Euclid (graphAmbientDimension d n r)) :=
  graphEuclideanEquiv d n r '' normalizedAnnularGraph d n r

def graphSetHomeomorph (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    normalizedAnnularGraph d n r ≃ₜ euclideanNormalizedGraph d n r :=
  (graphEuclideanEquiv d n r).toHomeomorph.image _

@[simp] theorem graphSetHomeomorph_val {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (z : normalizedAnnularGraph d n r) :
    (graphSetHomeomorph d n r z).val = graphEuclideanEquiv d n r z.val := rfl

theorem euclideanNormalizedGraph_hasSmoothEmbeddedCharts {d : ℕ} {n : Fin d → ℕ}
    {r : ℕ} (hd : 0 < d) :
    HasSmoothEmbeddedCharts (expectedDimension d n r) (euclideanNormalizedGraph d n r) := by
  intro z
  let h := graphSetHomeomorph d n r
  obtain ⟨e,u,hu,he,hsm,_hproj,hinj,_hc⟩ :=
    NormalizedGraphCharts.exists_normalizedGraph_chart hd (h.symm z)
  let c := e.transHomeomorph h
  refine ⟨c, ?_, ?_, ?_⟩
  · change h.symm z ∈ e.target
    rw [← he]
    exact e.map_source hu
  · change ContDiffOn ℝ 1
      (fun v => graphEuclideanEquiv d n r (e v).val) e.source
    exact (graphEuclideanEquiv d n r).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hsm.of_le (by simp))
  · intro v hv
    change Function.Injective (fderiv ℝ
      (fun w => graphEuclideanEquiv d n r (e w).val) v)
    have hdif : DifferentiableAt ℝ (fun w => (e w).val) v :=
      ((hsm.of_le (by simp)).contDiffAt (e.open_source.mem_nhds hv)).differentiableAt one_ne_zero
    have hchain := ((graphEuclideanEquiv d n r).toContinuousLinearEquiv.hasFDerivAt.comp v
      hdif.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => graphEuclideanEquiv d n r (e w).val) v =
      (graphEuclideanEquiv d n r).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fun w => (e w).val) v) at hchain
    rw [hchain]
    exact (graphEuclideanEquiv d n r).injective.comp (hinj v hv)

#assert_trust kernel euclideanNormalizedGraph_hasSmoothEmbeddedCharts
#print axioms euclideanNormalizedGraph_hasSmoothEmbeddedCharts
end NLA.Proofs.TR06
