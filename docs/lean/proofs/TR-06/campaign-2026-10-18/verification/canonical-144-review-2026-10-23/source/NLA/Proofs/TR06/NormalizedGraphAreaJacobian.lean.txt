import NLA.Proofs.TR06.NormalizedGraphCharts
import NLA.Proofs.TR06.ModelAngular
import NLA.TR06.AngularMeasurability

/-! Actual angular slope times input Jacobian is bounded by the genuine
Hilbert graph Jacobian on every constructed graph chart. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphArea
open scoped Topology ENNReal
open Set Filter MeasureTheory NLA.TR06 NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

set_option maxHeartbeats 1000000 in
theorem fderiv_branchMap (c : SmoothDecompositionChart d n r)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hv : v ∈ c.chart.source) :
    fderiv ℝ (branchMap c) v = pairedL2Map
      (fderiv ℝ (fun y => (c.chart y).val) v)
      (fderiv ℝ (fun y => normalizedTuple (c.summands y)) v) := by
  have hi : ContDiffAt ℝ 1 (fun y => (c.chart y).val) v :=
    (c.input_smooth.of_le (by simp)).contDiffAt (c.chart.open_source.mem_nhds hv)
  have ho : ContDiffAt ℝ 1 (fun y => normalizedTuple (c.summands y)) v :=
    (c.output_smooth.of_le (by simp)).contDiffAt (c.chart.open_source.mem_nhds hv)
  have hinput := hi.differentiableAt one_ne_zero
  have houtput := ho.differentiableAt one_ne_zero
  have hpair := hinput.hasFDerivAt.prodMk houtput.hasFDerivAt
  have h : HasFDerivAt (branchMap c) (pairedL2Map
      (fderiv ℝ (fun y => (c.chart y).val) v)
      (fderiv ℝ (fun y => normalizedTuple (c.summands y)) v)) v := by
    convert! (WithLp.prodContinuousLinearEquiv 2 ℝ (Tensor ℝ d n) (AngularOutput d n r)).symm.hasFDerivAt.comp
      v hpair using 1
  haveI : ContinuousSMul ℝ (NormalizedGraphAmbient d n r) := inferInstance
  exact h.fderiv

theorem branch_jacobian_bound (c : SmoothDecompositionChart d n r)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hv : v ∈ c.chart.source) :
    angularSlope r (c.chart v).val *
        ENNReal.ofReal ((fderiv ℝ (fun y => (c.chart y).val) v).toLinearMap.normDet) ≤
      ENNReal.ofReal ((fderiv ℝ (branchMap c) v).toLinearMap.normDet) := by
  rw [← smooth_chart_operatorNorm_eq_angularSlope c v hv,fderiv_branchMap c v hv]
  rw [← ENNReal.ofReal_mul (norm_nonneg (inducedDerivative
    (fderiv ℝ (fun y => (c.chart y).val) v)
    (fderiv ℝ (fun y => normalizedTuple (c.summands y)) v) (c.input_injective_derivative v hv)))]
  apply ENNReal.ofReal_le_ofReal
  exact opNorm_rangeInverseOperator_mul_normDet_le _ _ (c.input_injective_derivative v hv)

theorem graphChart_jacobian_bound
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
      (normalizedAnnularGraph d n r))
    (c : SmoothDecompositionChart d n r) (hsub : e.source ⊆ c.chart.source)
    (hformula : ∀ v ∈ e.source, (e v).val = branchMap c v)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hv : v ∈ e.source) :
    angularSlope r (e v).val.ofLp.1 *
        ENNReal.ofReal ((fderiv ℝ (fun y => (e y).val.ofLp.1) v).toLinearMap.normDet) ≤
      ENNReal.ofReal ((fderiv ℝ (fun y => (e y).val) v).toLinearMap.normDet) := by
  have heq : (fun y => (e y).val) =ᶠ[𝓝 v] branchMap c := by
    filter_upwards [e.open_source.mem_nhds hv] with y hy using hformula y hy
  have hinputeq : (fun y => (e y).val.ofLp.1) =ᶠ[𝓝 v] fun y => (c.chart y).val := by
    filter_upwards [e.open_source.mem_nhds hv] with y hy
    rw [hformula y hy]
    rfl
  have hbase : (e v).val.ofLp.1 = (c.chart v).val := by rw [hformula v hv]; rfl
  rw [heq.fderiv_eq,hinputeq.fderiv_eq,hbase]
  exact branch_jacobian_bound c v (hsub hv)

/-- A global Borel weight equal to the actual slope on every smooth regular
input. No global measurability of the exceptional-point slope is asserted. -/
theorem exists_measurable_slopeWeight :
    ∃ w : Tensor ℝ d n → ℝ≥0∞, Measurable w ∧
      ∀ A ∈ smoothRegularSet d n r, w A = angularSlope r A := by
  have hEmb := MeasurableEmbedding.subtype_coe (measurableSet_regularSet d n r)
  obtain ⟨w,hw,hEq⟩ := hEmb.exists_measurable_extend
    (measurable_angularSlope_regularSet (d := d) (n := n) (r := r)) (fun _ => ⟨0⟩)
  refine ⟨w,hw,fun A hA => ?_⟩
  exact congrFun hEq ⟨A,smoothRegularSet_subset_regularSet hA⟩

#assert_trust kernel fderiv_branchMap
#assert_trust kernel branch_jacobian_bound
#assert_trust kernel graphChart_jacobian_bound
#assert_trust kernel exists_measurable_slopeWeight
#print axioms graphChart_jacobian_bound
#print axioms exists_measurable_slopeWeight
end NLA.Proofs.TR06.NormalizedGraphArea
