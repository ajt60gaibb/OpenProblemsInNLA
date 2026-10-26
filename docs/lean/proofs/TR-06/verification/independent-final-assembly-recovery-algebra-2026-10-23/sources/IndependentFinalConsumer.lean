/- Original ten specification headers: copyright 2026 George Stepaniants, Apache-2.0.
Regenerated independently from the preserved published Challenge; no Challenge import. -/
import NLA.Proofs.TR06.RetainedBoundaryMean
import Reviewed.TR06
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set
namespace NLA.TR06

theorem independent_original_derivativeRatio_eq_operatorNorm {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (dφ : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (dg : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r)
    (hinj : Function.Injective dφ) :
    derivativeRatio dφ dg = ENNReal.ofReal ‖inducedDerivative dφ dg hinj‖ := by
  exact NLA.TR06.derivativeRatio_eq_operatorNorm dφ dg hinj
#assert_trust kernel independent_original_derivativeRatio_eq_operatorNorm
#print axioms independent_original_derivativeRatio_eq_operatorNorm

theorem independent_original_angularSlope_eq_chart_derivative {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : DecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    angularSlope r (c.chart u).val =
      derivativeRatio (fderiv ℝ (fun v => (c.chart v).val) u)
        (fderiv ℝ (fun v => normalizedTuple (c.summands v)) u) := by
  exact NLA.TR06.angularSlope_eq_chart_derivative c u hu
#assert_trust kernel independent_original_angularSlope_eq_chart_derivative
#print axioms independent_original_angularSlope_eq_chart_derivative

theorem independent_original_induced_volume_chart {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : DecompositionChart d n r)
    (s : Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))))
    (hs : MeasurableSet s) (hsub : s ⊆ c.chart.source) :
    (μHE[expectedDimension d n r] : Measure (Tensor ℝ d n))
      ((fun v => (c.chart v).val) '' s) =
    ∫⁻ v in s,
      ENNReal.ofReal ((fderiv ℝ (fun w => (c.chart w).val) v).toLinearMap.normDet) := by
  exact NLA.TR06.induced_volume_chart c s hs hsub
#assert_trust kernel independent_original_induced_volume_chart
#print axioms independent_original_induced_volume_chart

theorem independent_original_regular_locus {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : GenericComplexIdentifiable d n r) :
    MeasurableSet (identifiableRealSet d n r) ∧
    MeasurableSet (regularSet d n r) ∧
    regularSet d n r ⊆ identifiableRealSet d n r ∧
    tensorVolume d n r (identifiableRealSet d n r \ regularSet d n r) = 0 ∧
    regularVolume d n r Set.univ ≠ 0 := by
  exact NLA.TR06.regular_locus n r hd hn hr hgeneric
#assert_trust kernel independent_original_regular_locus
#print axioms independent_original_regular_locus

theorem independent_original_finite_angular_mean {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : GenericComplexIdentifiable d n r) :
    0 < normalization d n r ∧ normalization d n r < ⊤ ∧
    regularNormalization d n r = normalization d n r ∧
    regularInputMeasure d n r = inputMeasure d n r ∧
    IsProbabilityMeasure (regularInputMeasure d n r) ∧
    AEMeasurable (angularSlope (d := d) (n := n) r) (tensorVolume d n r) ∧
    (∫⁻ A, angularSlope r A ∂(inputMeasure d n r)) < ⊤ ∧
    (∫⁻ A, angularSlope r A ∂(regularInputMeasure d n r)) < ⊤ := by
  exact NLA.TR06.finite_angular_mean n r hd hn hr hgeneric
#assert_trust kernel independent_original_finite_angular_mean
#print axioms independent_original_finite_angular_mean

theorem independent_original_generic_iff_source (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    GenericComplexIdentifiable d n r ↔ SourceGenericComplexIdentifiable d n r := by
  exact NLA.TR06.generic_iff_source d n r
#assert_trust kernel independent_original_generic_iff_source
#print axioms independent_original_generic_iff_source

theorem independent_original_smooth_locus_correspondence {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    MeasurableSet (sourceSmoothSet d n r) ∧
    MeasurableSet (smoothRegularSet d n r) ∧
    smoothRegularSet d n r ⊆ sourceSmoothSet d n r ∧
    tensorVolume d n r (identifiableRealSet d n r \ smoothRegularSet d n r) = 0 ∧
    sourceVolume d n r = regularVolume d n r := by
  exact NLA.TR06.smooth_locus_correspondence n r hd hn hr hgeneric
#assert_trust kernel independent_original_smooth_locus_correspondence
#print axioms independent_original_smooth_locus_correspondence

theorem independent_original_smooth_chart_is_local_addition_inverse {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    IsLocalAdditionInverse c u := by
  exact NLA.TR06.smooth_chart_is_local_addition_inverse hd hn hr c u hu
#assert_trust kernel independent_original_smooth_chart_is_local_addition_inverse
#print axioms independent_original_smooth_chart_is_local_addition_inverse

theorem independent_original_source_model_correspondence {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    sourceNormalization d n r = normalization d n r ∧
    sourceInputMeasure d n r = inputMeasure d n r ∧
    (∀ᵐ A ∂(sourceVolume d n r), sourceAngular d n r A = angularSlope r A) := by
  exact NLA.TR06.source_model_correspondence n r hd hn hr hgeneric
#assert_trust kernel independent_original_source_model_correspondence
#print axioms independent_original_source_model_correspondence

theorem independent_original_finite_angular_mean_source {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    0 < sourceNormalization d n r ∧ sourceNormalization d n r < ⊤ ∧
    IsProbabilityMeasure (sourceInputMeasure d n r) ∧
    AEMeasurable (sourceAngular d n r) (sourceInputMeasure d n r) ∧
    (∫⁻ A, sourceAngular d n r A ∂(sourceInputMeasure d n r)) < ⊤ := by
  exact NLA.TR06.finite_angular_mean_source n r hd hn hr hgeneric
#assert_trust kernel independent_original_finite_angular_mean_source
#print axioms independent_original_finite_angular_mean_source

end NLA.TR06
namespace IndependentTR06Assembly
/-- Literal original quantifiers, true normalizer and true intrinsic numerator. -/
theorem intrinsic_literal :
    ∀ (d : ℕ) (dims : Fin d → ℕ) (r : ℕ),
      3 ≤ d → (∀ j : Fin d, 2 ≤ dims j) → 3 ≤ r →
      NLA.Statements.TR06.GenericComplexIdentifiable dims r →
      0 < NLA.Statements.TR06.Normalizer dims r ∧
      NLA.Statements.TR06.Normalizer dims r < ⊤ ∧
      NLA.Statements.TR06.AngularIntegral dims r /
        NLA.Statements.TR06.Normalizer dims r < ⊤ := by
  exact NLA.Proofs.TR06.target

theorem separately_reviewed_literal : NLA.ReviewedStatements.TR06.Target := by
  exact NLA.Proofs.TR06.target

#assert_trust kernel intrinsic_literal
#assert_trust kernel separately_reviewed_literal
#print axioms intrinsic_literal
#print axioms separately_reviewed_literal
end IndependentTR06Assembly
