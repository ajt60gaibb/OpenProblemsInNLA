import NLA.Proofs.TR06.ModelChartDerivative
import NLA.Proofs.TR06.UnramifiedDifferentialReal
import NLA.Proofs.TR06.NormalizedGraphRows

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology
namespace NLA.Proofs.TR06
open Set Filter NLA.TR06 NLA.TR06.Segre
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def normalizedPivotGraph (q : Fin r → TensorIndex d n) (z : Parameter ℝ q) :
    NormalizedGraphAmbient d n r := normalizedGraphPoint (sum q z) (summands q z)

def chartGraphParameter (c : SmoothDecompositionChart d n r)
    (q : Fin r → TensorIndex d n) (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) :
    Parameter ℝ q := UnramifiedDifferential.pivotParameterEquiv q (chartPivotMap c q u)

theorem chartGraphParameter_differentiableAt (c : SmoothDecompositionChart d n r)
    (q : Fin r → TensorIndex d n) (u : EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (hp : ∀ i, c.summands u i (q i) ≠ 0) :
    DifferentiableAt ℝ (chartGraphParameter c q) u :=
  (UnramifiedDifferential.pivotParameterEquiv q).differentiableAt.comp u
    ((chartPivotMap_contDiffAt c q u hu hp).differentiableAt one_ne_zero)

theorem chartGraphParameter_derivative_bijective (c : SmoothDecompositionChart d n r)
    (q : Fin r → TensorIndex d n) (u : EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (hp : ∀ i, c.summands u i (q i) ≠ 0) :
    Function.Bijective (fderiv ℝ (chartGraphParameter c q) u) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (expectedDimension d n r))) =
      Module.finrank ℝ (OrderedPivotData q) := by
    rw [finrank_euclideanSpace_fin,finrank_orderedPivotData]
  have hbij : Function.Bijective (fderiv ℝ (chartPivotMap c q) u) :=
    (fderiv ℝ (chartPivotMap c q) u).toLinearMap.linearEquivOfInjective
      (chartPivotMap_injective_derivative c q u hu hp) hdim |>.bijective
  have hchain := ((UnramifiedDifferential.pivotParameterEquiv q).hasFDerivAt.comp u
    ((chartPivotMap_contDiffAt c q u hu hp).differentiableAt one_ne_zero).hasFDerivAt).fderiv
  change fderiv ℝ (chartGraphParameter c q) u =
    (UnramifiedDifferential.pivotParameterEquiv q).toContinuousLinearMap.comp
      (fderiv ℝ (chartPivotMap c q) u) at hchain
  rw [hchain]
  exact (UnramifiedDifferential.pivotParameterEquiv q).bijective.comp hbij

theorem normalizedPivotGraph_chart_eventuallyEq (c : SmoothDecompositionChart d n r)
    (q : Fin r → TensorIndex d n) (u : EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (hp : ∀ i, c.summands u i (q i) ≠ 0) :
    (fun v => normalizedPivotGraph q (chartGraphParameter c q v)) =ᶠ[𝓝 u]
      NormalizedGraphCharts.branchMap c := by
  filter_upwards [Model.chart_decoder_eventuallyEq c q u hu hp,
    c.chart.open_source.mem_nhds hu] with v hv hvs
  have hsum : summands q (chartGraphParameter c q v) = c.summands v := by
    funext i
    rw [chartGraphParameter,UnramifiedDifferential.summands_pivotParameterEquiv]
    exact congrFun hv i
  unfold normalizedPivotGraph NormalizedGraphCharts.branchMap
  congr 1
  · change (∑ i, summands q (chartGraphParameter c q v) i) = (c.chart v).val
    rw [hsum]
    exact (c.decomposes v hvs).2

#assert_trust kernel chartGraphParameter_derivative_bijective
#assert_trust kernel normalizedPivotGraph_chart_eventuallyEq
#print axioms chartGraphParameter_derivative_bijective
#print axioms normalizedPivotGraph_chart_eventuallyEq
end NLA.Proofs.TR06
