import NLA.Proofs.TR06.ModelAngular
import NLA.TR06.Homogeneity
import NLA.TR06.AngularMeasurability

/-! Actual measurable positive-cone structure of the smooth decomposition
chart locus, and degree minus one angular homogeneity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators Topology ENNReal MeasureTheory
open MeasureTheory
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Scaling the whole actual identifiable sampling space is a homeomorphism. -/
def samplingScale (hd : 0 < d) (t : ℝ) (ht : t ≠ 0) :
    NLA.TR06.identifiableRealSet d n r ≃ₜ NLA.TR06.identifiableRealSet d n r where
  toFun A := ⟨t • A.val,(NLA.TR06.smul_mem_identifiableRealSet_iff hd A.val ht).mpr A.property⟩
  invFun A := ⟨t⁻¹ • A.val,(NLA.TR06.smul_mem_identifiableRealSet_iff hd A.val
    (inv_ne_zero ht)).mpr A.property⟩
  left_inv A := by ext; simp only [smul_smul,inv_mul_cancel₀ ht,one_smul]
  right_inv A := by ext; simp only [smul_smul,mul_inv_cancel₀ ht,one_smul]
  continuous_toFun := ((continuous_const : Continuous
    (fun _ : NLA.TR06.identifiableRealSet d n r => t)).smul continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_const : Continuous
    (fun _ : NLA.TR06.identifiableRealSet d n r => t⁻¹)).smul continuous_subtype_val).subtype_mk _

theorem scaled_chart_val (hd : 0 < d) (c : NLA.TR06.SmoothDecompositionChart d n r)
    (t : ℝ) (ht : t ≠ 0) (u : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r))) :
    ((c.chart.trans (samplingScale hd t ht).toOpenPartialHomeomorph) u).val =
      t • (c.chart u).val := by
  rw [OpenPartialHomeomorph.trans_apply,Homeomorph.toOpenPartialHomeomorph_apply]
  rfl

/-- A scaled chart is an actual embedded chart in the entire identifiable
space. Its normalized output is exactly the original output for positive t. -/
def scaleSmoothChart (hd : 0 < d) (c : NLA.TR06.SmoothDecompositionChart d n r)
    (t : ℝ) (ht : 0 < t) : NLA.TR06.SmoothDecompositionChart d n r where
  chart := c.chart.trans (samplingScale hd t ht.ne').toOpenPartialHomeomorph
  input_smooth := by
    simp_rw [scaled_chart_val]
    exact (c.input_smooth.const_smul t).mono (fun _ hu => hu.1)
  input_injective_derivative := by
    intro u hu
    simp_rw [scaled_chart_val]
    have hdiff := (c.input_smooth.contDiffAt
      (c.chart.open_source.mem_nhds hu.1)).differentiableAt (by simp)
    change Function.Injective (fderiv ℝ (t • fun y => (c.chart y).val) u)
    rw [(hdiff.hasFDerivAt.const_smul t).fderiv]
    intro x y hxy
    apply c.input_injective_derivative u hu.1
    have hxy' : t • (fderiv ℝ (fun y => (c.chart y).val) u x) =
        t • (fderiv ℝ (fun y => (c.chart y).val) u y) := hxy
    have h := congrArg (fun z : NLA.TR06.Tensor ℝ d n => t⁻¹ • z) hxy'
    simpa only [smul_smul,inv_mul_cancel₀ ht.ne',one_smul] using h
  summands u i := t • c.summands u i
  decomposes u hu := by
    rw [scaled_chart_val]
    exact NLA.TR06.decomposes_smul hd (c.decomposes u hu.1) ht.ne'
  summands_smooth i := (c.summands_smooth i).const_smul t |>.mono (fun _ hu => hu.1)
  output_smooth := by
    have heq : (fun u => NLA.TR06.normalizedTuple (fun i => t • c.summands u i)) =
        (fun u => NLA.TR06.normalizedTuple (c.summands u)) :=
      funext fun u => NLA.TR06.normalizedTuple_pos_smul (c.summands u) ht
    rw [heq]
    exact c.output_smooth.mono (fun _ hu => hu.1)

theorem pos_smul_mem_smoothRegular (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (A : NLA.TR06.Tensor ℝ d n) (hA : A ∈ NLA.TR06.smoothRegularSet d n r) :
    t • A ∈ NLA.TR06.smoothRegularSet d n r := by
  obtain ⟨c,u,hu,rfl⟩ := hA
  refine ⟨scaleSmoothChart hd c t ht,u,⟨hu,Set.mem_univ _⟩,?_⟩
  exact scaled_chart_val hd c t ht.ne' u

theorem pos_smul_mem_smoothRegular_iff (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (A : NLA.TR06.Tensor ℝ d n) :
    t • A ∈ NLA.TR06.smoothRegularSet d n r ↔ A ∈ NLA.TR06.smoothRegularSet d n r := by
  constructor
  · intro h
    simpa only [smul_smul,inv_mul_cancel₀ ht.ne',one_smul] using
      pos_smul_mem_smoothRegular hd t⁻¹ (inv_pos.mpr ht) (t • A) h
  · exact pos_smul_mem_smoothRegular hd t ht A

theorem measurableSet_smoothRegular :
    MeasurableSet (NLA.TR06.smoothRegularSet d n r) :=
  NLA.TR06.measurableSet_smoothRegularSet d n r

theorem zero_not_mem_smoothRegular (hr : 0 < r) :
    (0 : NLA.TR06.Tensor ℝ d n) ∉ NLA.TR06.smoothRegularSet d n r := by
  intro h
  have hsampling := NLA.TR06.smoothRegularSet_subset_identifiable h
  apply hsampling.1.2 0 hr
  refine ⟨Fin.elim0,?_⟩
  simp [NLA.TR06.Decomposes]

theorem aemeasurable_angularSlope_smoothVolume :
    AEMeasurable (NLA.TR06.angularSlope (d := d) (n := n) r)
      ((Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r)).restrict
        (NLA.TR06.smoothRegularSet d n r)) :=
  (NLA.TR06.aemeasurable_angularSlope_regularVolume d n r).mono_measure
    (Measure.restrict_mono_set _ NLA.TR06.smoothRegularSet_subset_regularSet)

theorem angularSlope_pos_smul (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (A : NLA.TR06.Tensor ℝ d n) :
    NLA.TR06.angularSlope r (t • A) = NLA.TR06.angularSlope r A / ENNReal.ofReal t :=
  NLA.TR06.angularSlope_pos_smul hd A ht

#assert_trust kernel samplingScale
#assert_trust kernel scaled_chart_val
#assert_trust kernel scaleSmoothChart
#assert_trust kernel pos_smul_mem_smoothRegular
#assert_trust kernel pos_smul_mem_smoothRegular_iff
#assert_trust kernel measurableSet_smoothRegular
#assert_trust kernel zero_not_mem_smoothRegular
#assert_trust kernel aemeasurable_angularSlope_smoothVolume
#assert_trust kernel angularSlope_pos_smul
#print axioms scaleSmoothChart
#print axioms pos_smul_mem_smoothRegular_iff
#print axioms zero_not_mem_smoothRegular
#print axioms aemeasurable_angularSlope_smoothVolume
end NLA.Proofs.TR06.Model
