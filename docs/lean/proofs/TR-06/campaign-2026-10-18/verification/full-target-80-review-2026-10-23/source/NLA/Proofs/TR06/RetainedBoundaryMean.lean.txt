import NLA.Proofs.TR06.Final
import NLA.Proofs.TR06.RetainedBoundaryLocus

/-! The exact two published finite-mean boundary declarations follow from
that same literal intrinsic target by the proved measure/derivative equalities. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set
namespace NLA.Proofs.TR06.RetainedBoundary
open NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Transport the literal intrinsic expectation to the literal normalized
metric-model law; no independent integrability premise is introduced. -/
theorem model_integrability_of_intrinsic_mean (j₀ : Fin d)
    (hfull : ∀ᵐ A ∂tensorVolume d n r, A ∈ smoothRegularSet d n r)
    (hmean : NLA.Statements.TR06.FiniteAngularMean n r) :
    0 < normalization d n r ∧ normalization d n r < ⊤ ∧
    (∫⁻ A, angularSlope r A ∂inputMeasure d n r) < ⊤ := by
  rcases hmean with ⟨hpos,hfinite,hangular⟩
  rw [Model.normalizer_eq_normalization j₀ hfull] at hpos hfinite
  rw [Model.angularIntegral_eq_weightedSlope j₀ hfull,
    Model.normalizer_eq_normalization j₀ hfull,
    ← Model.normalized_angularIntegral_eq hfull] at hangular
  exact ⟨hpos,hfinite,hangular⟩

#assert_trust kernel model_integrability_of_intrinsic_mean
#print axioms model_integrability_of_intrinsic_mean
end NLA.Proofs.TR06.RetainedBoundary

namespace NLA.TR06
open NLA.Proofs.TR06

/-- The unchanged complete published metric-model integrability target. -/
theorem finite_angular_mean {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : GenericComplexIdentifiable d n r) :
    0 < normalization d n r ∧ normalization d n r < ⊤ ∧
    regularNormalization d n r = normalization d n r ∧
    regularInputMeasure d n r = inputMeasure d n r ∧
    IsProbabilityMeasure (regularInputMeasure d n r) ∧
    AEMeasurable (angularSlope (d := d) (n := n) r) (tensorVolume d n r) ∧
    (∫⁻ A, angularSlope r A ∂(inputMeasure d n r)) < ⊤ ∧
    (∫⁻ A, angularSlope r A ∂(regularInputMeasure d n r)) < ⊤ := by
  have hn0 : ∀ j, 0 < n j := fun j => by have := hn j; omega
  have hfull := AlgebraicLocus.generic_smoothRegular_full_measure (by omega : 0 < d)
    hn0 (by omega : 2 ≤ r) hgeneric
  have hmean := NLA.Proofs.TR06.target d n r hd hn hr
    ((Model.generic_iff (d := d) (n := n) (r := r)).mpr hgeneric)
  obtain ⟨hpos,hfinite,hangular⟩ := RetainedBoundary.model_integrability_of_intrinsic_mean
    ⟨0,by omega⟩ hfull hmean
  have hlaw := Model.regularInputMeasure_eq_inputMeasure hfull
  refine ⟨hpos,hfinite,Model.regularNormalization_eq_normalization hfull,hlaw,?_,
    Model.aemeasurable_angularSlope_tensorVolume hfull,hangular,?_⟩
  · rw [hlaw]
    exact Model.inputMeasure_isProbability hpos hfinite
  · rw [hlaw]
    exact hangular

/-- The unchanged complete published source integrability and probability target. -/
theorem finite_angular_mean_source {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    0 < sourceNormalization d n r ∧ sourceNormalization d n r < ⊤ ∧
    IsProbabilityMeasure (sourceInputMeasure d n r) ∧
    AEMeasurable (sourceAngular d n r) (sourceInputMeasure d n r) ∧
    (∫⁻ A, sourceAngular d n r A ∂(sourceInputMeasure d n r)) < ⊤ := by
  have hgen := (generic_iff_source d n r).mpr hgeneric
  have hn0 : ∀ j, 0 < n j := fun j => by have := hn j; omega
  have hfull := AlgebraicLocus.generic_smoothRegular_full_measure (by omega : 0 < d)
    hn0 (by omega : 2 ≤ r) hgen
  have hmean := NLA.Proofs.TR06.target d n r hd hn hr
    ((Model.generic_iff (d := d) (n := n) (r := r)).mpr hgen)
  obtain ⟨hpos,hfinite,hangular⟩ := RetainedBoundary.model_integrability_of_intrinsic_mean
    ⟨0,by omega⟩ hfull hmean
  have hnorm := Model.sourceNormalization_eq_normalization hfull
  have hlaw := Model.sourceInputMeasure_eq_inputMeasure hfull
  refine ⟨by simpa only [hnorm] using hpos,by simpa only [hnorm] using hfinite,?_,?_,?_⟩
  · rw [hlaw]
    exact Model.inputMeasure_isProbability hpos hfinite
  · rw [hlaw]
    exact Model.aemeasurable_sourceAngular_inputMeasure hfull
  · rw [Model.normalized_sourceAngularIntegral_eq hfull,
      ← Model.normalized_angularIntegral_eq hfull]
    exact hangular

#assert_trust kernel finite_angular_mean
#assert_trust kernel finite_angular_mean_source
#print axioms finite_angular_mean
#print axioms finite_angular_mean_source
end NLA.TR06
