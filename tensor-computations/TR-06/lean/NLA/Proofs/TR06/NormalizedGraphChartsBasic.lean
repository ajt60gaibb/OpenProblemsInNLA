import NLA.Proofs.TR06.NormalizedGraphChartsSeparation
import NLA.Proofs.TR06.NormalizedGraphDefinitions
import NLA.TR06.LocusMeasurability

/-! Actual projections, branch smoothness, and branch alignment for the
normalized graph in its literal Hilbert ambient product. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphCharts
open scoped Topology
open Set NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def inputProjection : NormalizedGraphAmbient d n r →L[ℝ] Tensor ℝ d n :=
  (ContinuousLinearMap.fst ℝ (Tensor ℝ d n) (AngularOutput d n r)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Tensor ℝ d n) (AngularOutput d n r)).toContinuousLinearMap

def outputProjection : NormalizedGraphAmbient d n r →L[ℝ] AngularOutput d n r :=
  (ContinuousLinearMap.snd ℝ (Tensor ℝ d n) (AngularOutput d n r)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Tensor ℝ d n) (AngularOutput d n r)).toContinuousLinearMap

def graphInput (z : normalizedAnnularGraph d n r) : identifiableRealSet d n r :=
  ⟨z.val.ofLp.1,smoothRegularSet_subset_identifiable z.property.1⟩

theorem continuous_graphInput : Continuous (graphInput (d := d) (n := n) (r := r)) :=
  ((inputProjection (d := d) (n := n) (r := r)).continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_graphOutput : Continuous (fun z : normalizedAnnularGraph d n r => z.val.ofLp.2) :=
  (outputProjection (d := d) (n := n) (r := r)).continuous.comp continuous_subtype_val

def branchMap (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) : NormalizedGraphAmbient d n r :=
  normalizedGraphPoint (c.chart u).val (c.summands u)

theorem contDiffOn_branchMap (c : SmoothDecompositionChart d n r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchMap c) c.chart.source :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Tensor ℝ d n) (AngularOutput d n r)).symm.contDiff.comp_contDiffOn
    (c.input_smooth.prodMk c.output_smooth)

theorem branchMap_mem_graph (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (hann : (1/2 : ℝ) < ‖(c.chart u).val‖ ∧ ‖(c.chart u).val‖ < 3) :
    branchMap c u ∈ normalizedAnnularGraph d n r :=
  ⟨⟨c,u,hu,rfl⟩,hann.1,hann.2,c.summands u,c.decomposes u hu,rfl⟩

theorem exists_aligned_chart (z : normalizedAnnularGraph d n r) :
    ∃ (c : SmoothDecompositionChart d n r)
      (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))),
      u ∈ c.chart.source ∧ branchMap c u = z.val := by
  obtain ⟨hreg,_hl,_hu,a,ha,hout⟩ := z.property
  obtain ⟨c,u,hu,hcu⟩ := hreg
  have ha' : Decomposes a (c.chart u).val := by rwa [hcu]
  obtain ⟨σ,hσ⟩ := (c.chart u).property.2 (c.summands u) a (c.decomposes u hu) ha'
  refine ⟨permuteSmoothChart c σ,u,hu,?_⟩
  apply (WithLp.ofLp_injective (p := 2))
  apply Prod.ext
  · exact hcu
  · change normalizedTuple (c.summands u ∘ σ) = z.val.ofLp.2
    rw [hout]
    congr 1
    exact (funext hσ).symm

#assert_trust kernel inputProjection
#assert_trust kernel outputProjection
#assert_trust kernel graphInput
#assert_trust kernel continuous_graphInput
#assert_trust kernel continuous_graphOutput
#assert_trust kernel branchMap
#assert_trust kernel contDiffOn_branchMap
#assert_trust kernel branchMap_mem_graph
#assert_trust kernel exists_aligned_chart
#print axioms exists_aligned_chart
#print axioms contDiffOn_branchMap
end NLA.Proofs.TR06.NormalizedGraphCharts
