import NLA.Proofs.TR06.RetainedBoundaryMean
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set
namespace NLA.TR06
example {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (dφ : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (dg : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r)
    (hinj : Function.Injective dφ) :
    derivativeRatio dφ dg = ENNReal.ofReal ‖inducedDerivative dφ dg hinj‖ := @NLA.TR06.derivativeRatio_eq_operatorNorm d n r k dφ dg hinj
example {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : DecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    angularSlope r (c.chart u).val =
      derivativeRatio (fderiv ℝ (fun v => (c.chart v).val) u)
        (fderiv ℝ (fun v => normalizedTuple (c.summands v)) u) := @NLA.TR06.angularSlope_eq_chart_derivative d n r c u hu
example {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : DecompositionChart d n r)
    (s : Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))))
    (hs : MeasurableSet s) (hsub : s ⊆ c.chart.source) :
    (μHE[expectedDimension d n r] : Measure (Tensor ℝ d n))
      ((fun v => (c.chart v).val) '' s) =
    ∫⁻ v in s,
      ENNReal.ofReal ((fderiv ℝ (fun w => (c.chart w).val) v).toLinearMap.normDet) := @NLA.TR06.induced_volume_chart d n r c s hs hsub
example {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : GenericComplexIdentifiable d n r) :
    MeasurableSet (identifiableRealSet d n r) ∧
    MeasurableSet (regularSet d n r) ∧
    regularSet d n r ⊆ identifiableRealSet d n r ∧
    tensorVolume d n r (identifiableRealSet d n r \ regularSet d n r) = 0 ∧
    regularVolume d n r Set.univ ≠ 0 := @NLA.TR06.regular_locus d n r hd hn hr hgeneric
example {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : GenericComplexIdentifiable d n r) :
    0 < normalization d n r ∧ normalization d n r < ⊤ ∧
    regularNormalization d n r = normalization d n r ∧
    regularInputMeasure d n r = inputMeasure d n r ∧
    IsProbabilityMeasure (regularInputMeasure d n r) ∧
    AEMeasurable (angularSlope (d := d) (n := n) r) (tensorVolume d n r) ∧
    (∫⁻ A, angularSlope r A ∂(inputMeasure d n r)) < ⊤ ∧
    (∫⁻ A, angularSlope r A ∂(regularInputMeasure d n r)) < ⊤ := @NLA.TR06.finite_angular_mean d n r hd hn hr hgeneric
example (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    GenericComplexIdentifiable d n r ↔ SourceGenericComplexIdentifiable d n r := @NLA.TR06.generic_iff_source d n r
example {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    MeasurableSet (sourceSmoothSet d n r) ∧
    MeasurableSet (smoothRegularSet d n r) ∧
    smoothRegularSet d n r ⊆ sourceSmoothSet d n r ∧
    tensorVolume d n r (identifiableRealSet d n r \ smoothRegularSet d n r) = 0 ∧
    sourceVolume d n r = regularVolume d n r := @NLA.TR06.smooth_locus_correspondence d n r hd hn hr hgeneric
example {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    IsLocalAdditionInverse c u := @NLA.TR06.smooth_chart_is_local_addition_inverse d n r hd hn hr c u hu
example {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    sourceNormalization d n r = normalization d n r ∧
    sourceInputMeasure d n r = inputMeasure d n r ∧
    (∀ᵐ A ∂(sourceVolume d n r), sourceAngular d n r A = angularSlope r A) := @NLA.TR06.source_model_correspondence d n r hd hn hr hgeneric
example {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    0 < sourceNormalization d n r ∧ sourceNormalization d n r < ⊤ ∧
    IsProbabilityMeasure (sourceInputMeasure d n r) ∧
    AEMeasurable (sourceAngular d n r) (sourceInputMeasure d n r) ∧
    (∫⁻ A, sourceAngular d n r A ∂(sourceInputMeasure d n r)) < ⊤ := @NLA.TR06.finite_angular_mean_source d n r hd hn hr hgeneric
end NLA.TR06
