import NLA.Proofs.TR06.ModelGaussian

/-! Exact restoration of the retained C1/source volumes, Gaussian input laws,
and expectations from the actual full-measure smooth chart locus. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped ENNReal MeasureTheory
open MeasureTheory
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem regularVolume_eq_tensorVolume
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.regularVolume d n r = NLA.TR06.tensorVolume d n r := by
  have hreg := hfull.mono fun _ hA => NLA.TR06.smoothRegularSet_subset_regularSet hA
  have heq := Measure.restrict_eq_self_of_ae_mem hreg
  rw [NLA.TR06.tensorVolume,Measure.restrict_restrict_of_subset
    NLA.TR06.regularSet_subset_identifiable] at heq
  exact heq

theorem sourceVolume_eq_tensorVolume
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.sourceVolume d n r = NLA.TR06.tensorVolume d n r := by
  have hsource := hfull.mono fun _ hA => NLA.TR06.smoothRegularSet_subset_sourceSmoothSet hA
  have heq := Measure.restrict_eq_self_of_ae_mem hsource
  rw [NLA.TR06.tensorVolume,Measure.restrict_restrict_of_subset
    NLA.TR06.sourceSmoothSet_subset_identifiable] at heq
  exact heq

theorem regularNormalization_eq_normalization
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.regularNormalization d n r = NLA.TR06.normalization d n r := by
  unfold NLA.TR06.regularNormalization NLA.TR06.normalization NLA.TR06.unnormalizedInput
  rw [regularVolume_eq_tensorVolume hfull,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem sourceNormalization_eq_normalization
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.sourceNormalization d n r = NLA.TR06.normalization d n r := by
  unfold NLA.TR06.sourceNormalization NLA.TR06.normalization NLA.TR06.unnormalizedInput
  rw [sourceVolume_eq_tensorVolume hfull,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem regularInputMeasure_eq_inputMeasure
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.regularInputMeasure d n r = NLA.TR06.inputMeasure d n r := by
  unfold NLA.TR06.regularInputMeasure NLA.TR06.inputMeasure NLA.TR06.unnormalizedInput
  rw [regularNormalization_eq_normalization hfull,regularVolume_eq_tensorVolume hfull]

theorem sourceInputMeasure_eq_inputMeasure
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.sourceInputMeasure d n r = NLA.TR06.inputMeasure d n r := by
  unfold NLA.TR06.sourceInputMeasure NLA.TR06.inputMeasure NLA.TR06.unnormalizedInput
  rw [sourceNormalization_eq_normalization hfull,sourceVolume_eq_tensorVolume hfull]

theorem inputMeasure_isProbability
    (hpos : 0 < NLA.TR06.normalization d n r)
    (hfinite : NLA.TR06.normalization d n r < ⊤) :
    IsProbabilityMeasure (NLA.TR06.inputMeasure d n r) := by
  constructor
  change (NLA.TR06.normalization d n r)⁻¹ * NLA.TR06.normalization d n r = 1
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite.ne

theorem aemeasurable_angularSlope_tensorVolume
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    AEMeasurable (NLA.TR06.angularSlope (d := d) (n := n) r) (NLA.TR06.tensorVolume d n r) := by
  rw [← smoothVolume_eq_tensorVolume hfull]
  exact aemeasurable_angularSlope_smoothVolume

theorem inputMeasure_absolutelyContinuous :
    NLA.TR06.inputMeasure d n r ≪ NLA.TR06.tensorVolume d n r :=
  Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

theorem normalized_angularIntegral_eq
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    (∫⁻ A, NLA.TR06.angularSlope r A ∂NLA.TR06.inputMeasure d n r) =
      (∫⁻ A, NLA.TR06.angularSlope r A * NLA.TR06.gaussianWeight A
        ∂NLA.TR06.tensorVolume d n r) / NLA.TR06.normalization d n r := by
  have hg : Measurable (NLA.TR06.gaussianWeight (d := d) (n := n)) :=
    HomogeneousGaussian.measurable_gaussian
  unfold NLA.TR06.inputMeasure NLA.TR06.unnormalizedInput
  rw [lintegral_smul_measure,lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable
    (aemeasurable_angularSlope_tensorVolume hfull)]
  simp only [smul_eq_mul,Pi.mul_apply,div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  exact lintegral_congr fun A => mul_comm _ _

theorem sourceAngular_ae_eq_angularSlope
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.TR06.sourceAngular d n r =ᵐ[NLA.TR06.tensorVolume d n r] NLA.TR06.angularSlope r :=
  hfull.mono fun _ hA => NLA.TR06.sourceAngular_eq_angularSlope_on_smoothRegularSet hA

theorem aemeasurable_sourceAngular_inputMeasure
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    AEMeasurable (NLA.TR06.sourceAngular d n r) (NLA.TR06.inputMeasure d n r) := by
  have heq : NLA.TR06.sourceAngular d n r =ᵐ[NLA.TR06.inputMeasure d n r]
      NLA.TR06.angularSlope r :=
    inputMeasure_absolutelyContinuous.ae_le (sourceAngular_ae_eq_angularSlope hfull)
  exact ((aemeasurable_angularSlope_tensorVolume hfull).mono_ac
    inputMeasure_absolutelyContinuous).congr heq.symm

theorem normalized_sourceAngularIntegral_eq
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    (∫⁻ A, NLA.TR06.sourceAngular d n r A ∂NLA.TR06.sourceInputMeasure d n r) =
      (∫⁻ A, NLA.TR06.angularSlope r A * NLA.TR06.gaussianWeight A
        ∂NLA.TR06.tensorVolume d n r) / NLA.TR06.normalization d n r := by
  rw [sourceInputMeasure_eq_inputMeasure hfull,← normalized_angularIntegral_eq hfull]
  exact lintegral_congr_ae (inputMeasure_absolutelyContinuous.ae_le
    (sourceAngular_ae_eq_angularSlope hfull))

#assert_trust kernel regularVolume_eq_tensorVolume
#assert_trust kernel sourceVolume_eq_tensorVolume
#assert_trust kernel regularNormalization_eq_normalization
#assert_trust kernel sourceNormalization_eq_normalization
#assert_trust kernel regularInputMeasure_eq_inputMeasure
#assert_trust kernel sourceInputMeasure_eq_inputMeasure
#assert_trust kernel inputMeasure_isProbability
#assert_trust kernel aemeasurable_angularSlope_tensorVolume
#assert_trust kernel inputMeasure_absolutelyContinuous
#assert_trust kernel normalized_angularIntegral_eq
#assert_trust kernel sourceAngular_ae_eq_angularSlope
#assert_trust kernel aemeasurable_sourceAngular_inputMeasure
#assert_trust kernel normalized_sourceAngularIntegral_eq
#print axioms normalized_angularIntegral_eq
#print axioms normalized_sourceAngularIntegral_eq
end NLA.Proofs.TR06.Model
