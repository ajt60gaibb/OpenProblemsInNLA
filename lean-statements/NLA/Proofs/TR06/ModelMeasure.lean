import NLA.Proofs.TR06.ModelAngular
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Transfer of the actual Hausdorff-volume Gaussian quantities. The only
geometric premise is the separately required full-measure smooth-chart locus;
no equality of the two regular loci at every exceptional point is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped ENNReal MeasureTheory
open MeasureTheory
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem inducedVolume_eq_tensorVolume (j₀ : Fin d)
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.Statements.TR06.InducedVolume n r = NLA.TR06.tensorVolume d n r := by
  have hintrinsic : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ {A | NLA.Statements.TR06.SmoothIdentifiable n r A} :=
    hfull.mono fun _ hA => smoothRegular_subset_intrinsic j₀ hA
  have heq := Measure.restrict_eq_self_of_ae_mem hintrinsic
  rw [NLA.TR06.tensorVolume,Measure.restrict_restrict_of_subset
    smoothIdentifiable_subset_sampling] at heq
  exact heq

theorem angularCondition_ae_eq_angularSlope (j₀ : Fin d)
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.Statements.TR06.AngularCondition r =ᵐ[NLA.TR06.tensorVolume d n r]
      NLA.TR06.angularSlope r :=
  hfull.mono fun A hA => angularCondition_eq_angularSlope_on_smoothRegular j₀ A hA

theorem normalizer_eq_normalization (j₀ : Fin d)
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.Statements.TR06.Normalizer n r = NLA.TR06.normalization d n r := by
  unfold NLA.Statements.TR06.Normalizer NLA.TR06.normalization NLA.TR06.unnormalizedInput
  rw [inducedVolume_eq_tensorVolume j₀ hfull,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rfl

theorem angularIntegral_eq_weightedSlope (j₀ : Fin d)
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.Statements.TR06.AngularIntegral n r =
      ∫⁻ A, NLA.TR06.angularSlope r A * NLA.TR06.gaussianWeight A
        ∂NLA.TR06.tensorVolume d n r := by
  unfold NLA.Statements.TR06.AngularIntegral
  rw [inducedVolume_eq_tensorVolume j₀ hfull]
  apply lintegral_congr_ae
  exact (angularCondition_ae_eq_angularSlope j₀ hfull).mono fun A hA =>
    congrArg (fun z => z * NLA.TR06.gaussianWeight A) hA

/-- Exact final intrinsic finite-expectation transfer from the actual weighted
numerator and normalizer. All geometric/integrability obligations remain
explicit until supplied by their own proofs. -/
theorem finiteAngularMean_of_weightedSlope (j₀ : Fin d)
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r)
    (hpos : 0 < NLA.TR06.normalization d n r)
    (hfinite : NLA.TR06.normalization d n r < ⊤)
    (hangular : (∫⁻ A, NLA.TR06.angularSlope r A * NLA.TR06.gaussianWeight A
      ∂NLA.TR06.tensorVolume d n r) < ⊤) :
    NLA.Statements.TR06.FiniteAngularMean n r := by
  unfold NLA.Statements.TR06.FiniteAngularMean
  rw [normalizer_eq_normalization j₀ hfull,angularIntegral_eq_weightedSlope j₀ hfull]
  exact ⟨hpos,hfinite,ENNReal.div_lt_top hangular.ne hpos.ne'⟩

#assert_trust kernel inducedVolume_eq_tensorVolume
#assert_trust kernel angularCondition_ae_eq_angularSlope
#assert_trust kernel normalizer_eq_normalization
#assert_trust kernel angularIntegral_eq_weightedSlope
#assert_trust kernel finiteAngularMean_of_weightedSlope
#print axioms inducedVolume_eq_tensorVolume
#print axioms finiteAngularMean_of_weightedSlope
end NLA.Proofs.TR06.Model
