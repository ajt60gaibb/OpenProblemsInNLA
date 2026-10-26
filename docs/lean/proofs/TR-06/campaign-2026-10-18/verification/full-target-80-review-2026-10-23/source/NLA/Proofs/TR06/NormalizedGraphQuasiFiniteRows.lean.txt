import NLA.Proofs.TR06.NormalizedGraphParameter
import NLA.Proofs.TR06.GraphProjectionOrdered
import NLA.Proofs.TR06.ControlledProjectionDerivative

/-! Literal selected rows and the full chart-to-pivot tangent transport. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology BigOperators
namespace NLA.Proofs.TR06
open Set Filter NLA.TR06 NLA.TR06.Segre NLA.TR06.Area.Proposed
open GraphAlgebra GraphCharacter GraphProjection NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}

theorem normalizedPivotGraph_rows
    (σ : Fin k ↪ Fin (graphAmbientDimension d n r))
    (q : Fin r → TensorIndex d n) (p : Parameter ℝ q) :
    rowProjectedValues q (graphProjectionRows σ) p =
      (coordProjection σ (graphEuclideanEquiv d n r (normalizedPivotGraph q p))).ofLp := by
  have hdecode : graphCoordinateDecode (realGraphValues q p) = normalizedPivotGraph q p := by
    rfl
  funext j
  rw [rowProjectedValues,graphProjectionRows_apply,hdecode]

theorem chart_rowProjected_derivative_injective
    (σ : Fin k ↪ Fin (graphAmbientDimension d n r))
    (c : SmoothDecompositionChart d n r) (q : Fin r → TensorIndex d n)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (hp : ∀ i, c.summands u i (q i) ≠ 0)
    (hinj : Function.Injective (fderiv ℝ
      (fun v => coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))) u)) :
    Function.Injective (fderiv ℝ (rowProjectedValues q (graphProjectionRows σ))
      (chartGraphParameter c q u)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)
  have hbranch : DifferentiableAt ℝ (branchMap c) u :=
    ((contDiffOn_branchMap c).of_le (by simp) |>.contDiffAt
      (c.chart.open_source.mem_nhds hu)).differentiableAt one_ne_zero
  have hproject : DifferentiableAt ℝ
      (fun v => coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))) u :=
    (coordProjectionL σ).differentiableAt.comp u
      ((graphEuclideanEquiv d n r).toContinuousLinearEquiv.differentiableAt.comp u hbranch)
  have hflat := (e.hasFDerivAt.comp u hproject.hasFDerivAt).fderiv
  change fderiv ℝ
      (fun v => (coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))).ofLp) u =
    e.toContinuousLinearMap.comp
      (fderiv ℝ (fun v => coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))) u) at hflat
  have hflatInj : Function.Injective (fderiv ℝ
      (fun v => (coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))).ofLp) u) := by
    rw [hflat]
    exact e.injective.comp hinj
  have hlocal : (fun v => rowProjectedValues q (graphProjectionRows σ)
      (chartGraphParameter c q v)) =ᶠ[𝓝 u]
      (fun v => (coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))).ofLp) := by
    filter_upwards [normalizedPivotGraph_chart_eventuallyEq c q u hu hp] with v hv
    rw [normalizedPivotGraph_rows,hv]
  have hamp : ∀ i, chartGraphParameter c q u ⟨i,none⟩ ≠ 0 := by
    intro i
    exact hp i
  have hcomp := ((differentiableAt_rowProjectedValues q (graphProjectionRows σ)
    (chartGraphParameter c q u) hamp).hasFDerivAt.comp u
      (chartGraphParameter_differentiableAt c q u hu hp).hasFDerivAt).fderiv
  change fderiv ℝ (fun v => rowProjectedValues q (graphProjectionRows σ)
      (chartGraphParameter c q v)) u =
    (fderiv ℝ (rowProjectedValues q (graphProjectionRows σ))
      (chartGraphParameter c q u)).comp (fderiv ℝ (chartGraphParameter c q) u) at hcomp
  have hcomposition : Function.Injective
      ((fderiv ℝ (rowProjectedValues q (graphProjectionRows σ))
        (chartGraphParameter c q u)).comp (fderiv ℝ (chartGraphParameter c q) u)) := by
    rw [← hcomp,hlocal.fderiv_eq]
    exact hflatInj
  have hsurj := (chartGraphParameter_derivative_bijective c q u hu hp).surjective
  intro x y hxy
  obtain ⟨v,rfl⟩ := hsurj x
  obtain ⟨w,rfl⟩ := hsurj y
  exact congrArg (fderiv ℝ (chartGraphParameter c q) u) (hcomposition hxy)

#assert_trust kernel normalizedPivotGraph_rows
#assert_trust kernel chart_rowProjected_derivative_injective
#print axioms chart_rowProjected_derivative_injective
end NLA.Proofs.TR06
