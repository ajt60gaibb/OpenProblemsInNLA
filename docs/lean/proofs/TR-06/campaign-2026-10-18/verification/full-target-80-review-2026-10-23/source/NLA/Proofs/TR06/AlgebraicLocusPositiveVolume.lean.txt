import NLA.Proofs.TR06.AlgebraicLocusFullMeasure
import NLA.Proofs.TR06.ModelCone
import NLA.Proofs.TR06.HomogeneousGaussianScaling

/-! Positive expected-dimensional annular Hausdorff volume, obtained from an
actual regular chart and an invertible projected derivative. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.AlgebraicLocus
open scoped BigOperators ENNReal MeasureTheory Topology
open MeasureTheory Set Filter NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- An actual chart point in an open ambient set gives positive intrinsic
Hausdorff volume. The auxiliary projection uses the chart dimension, not the
ambient tensor dimension. -/
theorem chart_open_inter_volume_pos (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (U : Set (Tensor ℝ d n)) (hU : IsOpen U) (hbase : (c.chart u).val ∈ U) :
    0 < (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (smoothRegularSet d n r ∩ U) := by
  let E := EuclideanSpace ℝ (Fin (expectedDimension d n r))
  let f : E → Tensor ℝ d n := fun y => (c.chart y).val
  have hf : ContDiffAt ℝ 1 f u := (c.input_smooth.of_le (by simp)).contDiffAt
    (c.chart.open_source.mem_nhds hu)
  obtain ⟨L,hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (c.input_injective_derivative u hu)
  let g : E → E := fun y => L (f y)
  have hg : ContDiffAt ℝ 1 g u := L.contDiff.contDiffAt.comp u hf
  have hLg : L.comp (fderiv ℝ f u) = (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) := by
    apply ContinuousLinearMap.ext
    intro x
    exact hL x
  have hgderiv : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) u := by
    rw [← hLg]
    exact L.hasFDerivAt.comp u (hf.differentiableAt one_ne_zero).hasFDerivAt
  let e := hg.toOpenPartialHomeomorph g hgderiv one_ne_zero
  have hue : u ∈ e.source := hg.mem_toOpenPartialHomeomorph_source hgderiv one_ne_zero
  let W := e.source ∩ (c.chart.source ∩ f ⁻¹' U)
  have hW : IsOpen W := e.open_source.inter
    (c.input_smooth.continuousOn.isOpen_inter_preimage c.chart.open_source hU)
  have huW : u ∈ W := ⟨hue,hu,hbase⟩
  have hpos : 0 < (volume : Measure E) (e '' W) :=
    (e.isOpen_image_of_subset_source hW (fun _ h => h.1)).measure_pos volume
      ⟨e u,u,huW,rfl⟩
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hsubset : f '' W ⊆ smoothRegularSet d n r ∩ U := by
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨⟨c,y,hy.2.1,rfl⟩,hy.2.2⟩
  have hnull := measure_mono_null hsubset hzero
  have hbound := Area.euclidean_image_le_of_lipschitzOn
    (s := f '' W) L.lipschitz.lipschitzOnWith (expectedDimension d n r)
  rw [hnull,mul_zero] at hbound
  have heimage : e '' W = L '' (f '' W) := by
    rw [Set.image_image]
    rfl
  have hnullE : (Measure.euclideanHausdorffMeasure (expectedDimension d n r) : Measure E)
      (e '' W) = 0 := by
    rw [heimage]
    exact le_antisymm hbound bot_le
  have hμ : (Measure.euclideanHausdorffMeasure (expectedDimension d n r) : Measure E) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := E)
    simpa only [E,finrank_euclideanSpace_fin] using h
  rw [hμ] at hnullE
  exact hpos.ne' hnullE

theorem smooth_annular_volume_pos_of_nonempty (hd : 0 < d) (hr : 0 < r)
    (hne : (smoothRegularSet d n r).Nonempty) :
    0 < (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (HomogeneousGaussian.annulus (smoothRegularSet d n r)) := by
  obtain ⟨A,hA⟩ := hne
  have hA0 : A ≠ 0 := by rintro rfl; exact Model.zero_not_mem_smoothRegular hr hA
  let t : ℝ := (3/2) / ‖A‖
  have ht : 0 < t := div_pos (by norm_num) (norm_pos_iff.mpr hA0)
  have hscaled := Model.pos_smul_mem_smoothRegular hd t ht A hA
  have hnorm : ‖t • A‖ = 3/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hA0)
  obtain ⟨c,u,hu,hcu⟩ := hscaled
  let U : Set (Tensor ℝ d n) := {B | 1 < ‖B‖ ∧ ‖B‖ < 2}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hbase : (c.chart u).val ∈ U := by
    change 1 < ‖(c.chart u).val‖ ∧ ‖(c.chart u).val‖ < 2
    rw [hcu,hnorm]
    norm_num
  have hpos := chart_open_inter_volume_pos c u hu U hU hbase
  exact hpos.trans_le (measure_mono (fun B hB => ⟨hB.1,hB.2.1.le,hB.2.2⟩))

theorem generic_smooth_annular_volume_pos (hd : 0 < d) (hn : ∀ j, 0 < n j)
    (hr : 2 ≤ r) (hgeneric : GenericComplexIdentifiable d n r) :
    0 < (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (HomogeneousGaussian.annulus (smoothRegularSet d n r)) :=
  smooth_annular_volume_pos_of_nonempty hd (by omega)
    (generic_smoothRegular_nonempty hd hn hr hgeneric)

#assert_trust kernel chart_open_inter_volume_pos
#assert_trust kernel smooth_annular_volume_pos_of_nonempty
#assert_trust kernel generic_smooth_annular_volume_pos
#print axioms chart_open_inter_volume_pos
#print axioms generic_smooth_annular_volume_pos
end NLA.Proofs.TR06.AlgebraicLocus
