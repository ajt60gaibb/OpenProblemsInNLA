import NLA.Proofs.TR06.AlgebraicLocusPositiveVolume
import NLA.Proofs.TR06.ModelMeasureRestoration
import NLA.TR06.Generic
import NLA.TR06.Area

/-! The exact published TR-06 locus and source-law boundary declarations.
The original five already-proved boundary names remain in retained sources. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set
namespace NLA.TR06
open NLA.Proofs.TR06

/-- The exact original regular-locus target, with full-measure restoration and
positive induced volume derived from the original genericity hypothesis. -/
theorem regular_locus {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : GenericComplexIdentifiable d n r) :
    MeasurableSet (identifiableRealSet d n r) ∧
    MeasurableSet (regularSet d n r) ∧
    regularSet d n r ⊆ identifiableRealSet d n r ∧
    tensorVolume d n r (identifiableRealSet d n r \ regularSet d n r) = 0 ∧
    regularVolume d n r Set.univ ≠ 0 := by
  have hd0 : 0 < d := by omega
  have hn0 : ∀ j, 0 < n j := fun j => by have := hn j; omega
  have hr2 : 2 ≤ r := by omega
  have hfull := AlgebraicLocus.generic_smoothRegular_full_measure hd0 hn0 hr2 hgeneric
  have hregular := hfull.mono fun _ hA => smoothRegularSet_subset_regularSet hA
  have hnull : tensorVolume d n r (identifiableRealSet d n r \ regularSet d n r) = 0 :=
    measure_mono_null (fun _ h => h.2) (ae_iff.mp hregular)
  have hann := AlgebraicLocus.generic_smooth_annular_volume_pos hd0 hn0 hr2 hgeneric
  have hsmooth : 0 < (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (smoothRegularSet d n r) := hann.trans_le (measure_mono inter_subset_left)
  refine ⟨measurableSet_identifiableRealSet d n r,measurableSet_regularSet d n r,
    regularSet_subset_identifiable,hnull,?_⟩
  rw [Model.regularVolume_eq_tensorVolume hfull,← Model.smoothVolume_eq_tensorVolume hfull,
    Measure.restrict_apply_univ]
  exact hsmooth.ne'

/-- The exact original source/smooth-locus boundary target. -/
theorem smooth_locus_correspondence {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    MeasurableSet (sourceSmoothSet d n r) ∧
    MeasurableSet (smoothRegularSet d n r) ∧
    smoothRegularSet d n r ⊆ sourceSmoothSet d n r ∧
    tensorVolume d n r (identifiableRealSet d n r \ smoothRegularSet d n r) = 0 ∧
    sourceVolume d n r = regularVolume d n r := by
  have hgen := (generic_iff_source d n r).mpr hgeneric
  have hn0 : ∀ j, 0 < n j := fun j => by have := hn j; omega
  have hfull := AlgebraicLocus.generic_smoothRegular_full_measure (by omega : 0 < d)
    hn0 (by omega : 2 ≤ r) hgen
  refine ⟨measurableSet_sourceSmoothSet d n r,measurableSet_smoothRegularSet d n r,
    smoothRegularSet_subset_sourceSmoothSet,?_,?_⟩
  · exact measure_mono_null (fun _ h => h.2) (ae_iff.mp hfull)
  · rw [Model.sourceVolume_eq_tensorVolume hfull,Model.regularVolume_eq_tensorVolume hfull]

/-- The exact original normalized source-law and angular correspondence. -/
theorem source_model_correspondence {d : ℕ} (n : Fin d → ℕ) (r : ℕ)
    (hd : 3 ≤ d) (hn : ∀ j, 2 ≤ n j) (hr : 3 ≤ r)
    (hgeneric : SourceGenericComplexIdentifiable d n r) :
    sourceNormalization d n r = normalization d n r ∧
    sourceInputMeasure d n r = inputMeasure d n r ∧
    (∀ᵐ A ∂(sourceVolume d n r), sourceAngular d n r A = angularSlope r A) := by
  have hgen := (generic_iff_source d n r).mpr hgeneric
  have hn0 : ∀ j, 0 < n j := fun j => by have := hn j; omega
  have hfull := AlgebraicLocus.generic_smoothRegular_full_measure (by omega : 0 < d)
    hn0 (by omega : 2 ≤ r) hgen
  refine ⟨Model.sourceNormalization_eq_normalization hfull,
    Model.sourceInputMeasure_eq_inputMeasure hfull,?_⟩
  rw [Model.sourceVolume_eq_tensorVolume hfull]
  exact Model.sourceAngular_ae_eq_angularSlope hfull

#assert_trust kernel derivativeRatio_eq_operatorNorm
#assert_trust kernel angularSlope_eq_chart_derivative
#assert_trust kernel induced_volume_chart
#assert_trust kernel generic_iff_source
#assert_trust kernel smooth_chart_is_local_addition_inverse
#assert_trust kernel regular_locus
#assert_trust kernel smooth_locus_correspondence
#assert_trust kernel source_model_correspondence
#print axioms regular_locus
#print axioms smooth_locus_correspondence
#print axioms source_model_correspondence
end NLA.TR06
