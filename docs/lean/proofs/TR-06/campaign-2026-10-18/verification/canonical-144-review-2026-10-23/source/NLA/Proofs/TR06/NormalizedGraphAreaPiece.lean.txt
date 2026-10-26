import NLA.Proofs.TR06.NormalizedGraphAreaPartition
import NLA.Proofs.TR06.NormalizedGraphAreaJacobian
import NLA.Proofs.TR06.NormalizedGraphAreaWeighted

/-! Literal weighted input area is bounded by the area of one selected actual
graph branch, on every measurable subordinate input piece. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphArea
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set Filter NLA.TR06 NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def InputGraphChart.parameterPiece (C : InputGraphChart d n r) (P : Set (Tensor ℝ d n)) :
    Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))) :=
  C.graph.source ∩ C.input ⁻¹' P

def InputGraphChart.graphPiece (C : InputGraphChart d n r) (P : Set (Tensor ℝ d n)) :
    Set (NormalizedGraphAmbient d n r) :=
  (fun v => (C.graph v).val) '' C.parameterPiece P

theorem InputGraphChart.parameterPiece_measurable (C : InputGraphChart d n r)
    (P : Set (Tensor ℝ d n)) (hP : MeasurableSet P) : MeasurableSet (C.parameterPiece P) := by
  have hm := hP.preimage C.input_continuousOn.domRestrict.measurable
  have heq : Subtype.val '' ((C.graph.source.domRestrict C.input) ⁻¹' P) = C.parameterPiece P := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hPx⟩
      exact ⟨⟨x,hx⟩,hPx,rfl⟩
  rw [← heq]
  exact C.graph.open_source.measurableSet.subtype_image hm

theorem InputGraphChart.input_parameterPiece (C : InputGraphChart d n r)
    (P : Set (Tensor ℝ d n)) (hPsub : P ⊆ C.inputImage) :
    C.input '' C.parameterPiece P = P := by
  apply subset_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact hv.2
  · intro A hA
    obtain ⟨v,hv,hvA⟩ := hPsub hA
    exact ⟨v,⟨hv,by simpa only [mem_preimage, hvA] using hA⟩,hvA⟩

theorem InputGraphChart.graphPiece_subset (C : InputGraphChart d n r)
    (P : Set (Tensor ℝ d n)) : C.graphPiece P ⊆ normalizedAnnularGraph d n r := by
  rintro _ ⟨v,_hv,rfl⟩
  exact (C.graph v).property

theorem InputGraphChart.inputProjection_mem_piece (C : InputGraphChart d n r)
    (P : Set (Tensor ℝ d n)) (z : NormalizedGraphAmbient d n r) (hz : z ∈ C.graphPiece P) :
    inputProjection z ∈ P := by
  obtain ⟨v,hv,rfl⟩ := hz
  change inputProjection (C.graph v).val ∈ P
  rw [C.formula v hv.1]
  exact hv.2

theorem InputGraphChart.graphPiece_measurable (C : InputGraphChart d n r)
    (P : Set (Tensor ℝ d n)) (hP : MeasurableSet P) : MeasurableSet (C.graphPiece P) := by
  apply Area.image_measurable (C.parameterPiece_measurable P hP)
  · intro v hv
    have hb : ContDiffAt ℝ 1 (fun y => (C.graph y).val) v :=
      (C.smooth.of_le (by simp)).contDiffAt (C.graph.open_source.mem_nhds hv.1)
    exact (hb.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  · intro x hx y hy hxy
    exact C.graph.injOn hx.1 hy.1 (Subtype.ext hxy)

theorem InputGraphChart.jacobian_bound (C : InputGraphChart d n r)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hv : v ∈ C.graph.source) :
    angularSlope r (C.input v) *
        ENNReal.ofReal ((fderiv ℝ C.input v).toLinearMap.normDet) ≤
      ENNReal.ofReal ((fderiv ℝ (fun y => (C.graph y).val) v).toLinearMap.normDet) := by
  have h := graphChart_jacobian_bound C.graph C.original C.source_subset C.formula v hv
  have heq : (fun y => (C.graph y).val.ofLp.1) =ᶠ[𝓝 v] C.input := by
    filter_upwards [C.graph.open_source.mem_nhds hv] with y hy
    rw [C.formula y hy]
    rfl
  have hbase : (C.graph v).val.ofLp.1 = C.input v := by rw [C.formula v hv]; rfl
  rwa [heq.fderiv_eq,hbase] at h

theorem InputGraphChart.piece_angularIntegral_le_graphVolume (C : InputGraphChart d n r)
    (P : Set (Tensor ℝ d n)) (hP : MeasurableSet P) (hPsub : P ⊆ C.inputImage) :
    (∫⁻ A in P, angularSlope r A
      ∂(Measure.euclideanHausdorffMeasure (expectedDimension d n r))) ≤
      (Measure.euclideanHausdorffMeasure (expectedDimension d n r)) (C.graphPiece P) := by
  let s := C.parameterPiece P
  have hs : MeasurableSet s := C.parameterPiece_measurable P hP
  have hssource : s ⊆ C.graph.source := inter_subset_left
  have hinputSmooth : ContDiffOn ℝ 1 C.input C.graph.source :=
    (C.original.input_smooth.of_le (by simp)).mono C.source_subset
  have hinputDeriv : ∀ v ∈ C.graph.source, Function.Injective (fderiv ℝ C.input v) :=
    fun v hv => C.original.input_injective_derivative v (C.source_subset hv)
  obtain ⟨w,hw,hweight⟩ := exists_measurable_slopeWeight (d := d) (n := n) (r := r)
  have hwP (A : Tensor ℝ d n) (hA : A ∈ P) : w A = angularSlope r A := by
    obtain ⟨v,hv,rfl⟩ := hPsub hA
    exact hweight _ ⟨C.original,v,C.source_subset hv,rfl⟩
  have hwv (v : EuclideanSpace ℝ (Fin (expectedDimension d n r)))
      (hv : v ∈ C.graph.source) : w (C.input v) = angularSlope r (C.input v) :=
    hweight _ ⟨C.original,v,C.source_subset hv,rfl⟩
  have hweighted := open_immersion_lintegral C.graph.open_source C.input hinputSmooth hs
    hssource C.input_injOn hinputDeriv w hw
  simp only [finrank_euclideanSpace_fin] at hweighted
  rw [C.input_parameterPiece P hPsub] at hweighted
  have hgraphArea : (Measure.euclideanHausdorffMeasure (expectedDimension d n r)) (C.graphPiece P) =
      ∫⁻ v in s, ENNReal.ofReal ((fderiv ℝ (fun y => (C.graph y).val) v).toLinearMap.normDet) := by
    have hf : ∀ v ∈ s, HasFDerivWithinAt (fun y => (C.graph y).val)
        (fderiv ℝ (fun y => (C.graph y).val) v) s v := by
      intro v hv
      have hb : ContDiffAt ℝ 1 (fun y => (C.graph y).val) v :=
        (C.smooth.of_le (by simp)).contDiffAt (C.graph.open_source.mem_nhds hv.1)
      exact (hb.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    have hi : ∀ v ∈ s, Function.Injective (fderiv ℝ (fun y => (C.graph y).val) v) :=
      fun v hv => C.derivative_injective v hv.1
    have hinj : InjOn (fun y => (C.graph y).val) s := by
      intro x hx y hy hxy
      exact C.graph.injOn hx.1 hy.1 (Subtype.ext hxy)
    simpa only [finrank_euclideanSpace_fin, InputGraphChart.graphPiece, s] using
      (Area.immersion_area hs hf hi hinj)
  calc
    _ = ∫⁻ A in P, w A ∂(Measure.euclideanHausdorffMeasure (expectedDimension d n r)) :=
      setLIntegral_congr_fun hP (fun A hA => (hwP A hA).symm)
    _ = ∫⁻ v in s, ENNReal.ofReal ((fderiv ℝ C.input v).toLinearMap.normDet) * w (C.input v) := hweighted
    _ ≤ ∫⁻ v in s, ENNReal.ofReal ((fderiv ℝ (fun y => (C.graph y).val) v).toLinearMap.normDet) := by
      apply setLIntegral_mono' hs
      intro v hv
      rw [hwv v hv.1,mul_comm]
      exact C.jacobian_bound v hv.1
    _ = _ := hgraphArea.symm

#assert_trust kernel InputGraphChart.parameterPiece
#assert_trust kernel InputGraphChart.graphPiece
#assert_trust kernel InputGraphChart.parameterPiece_measurable
#assert_trust kernel InputGraphChart.input_parameterPiece
#assert_trust kernel InputGraphChart.graphPiece_subset
#assert_trust kernel InputGraphChart.inputProjection_mem_piece
#assert_trust kernel InputGraphChart.graphPiece_measurable
#assert_trust kernel InputGraphChart.jacobian_bound
#assert_trust kernel InputGraphChart.piece_angularIntegral_le_graphVolume
#print axioms InputGraphChart.piece_angularIntegral_le_graphVolume
end NLA.Proofs.TR06.NormalizedGraphArea
