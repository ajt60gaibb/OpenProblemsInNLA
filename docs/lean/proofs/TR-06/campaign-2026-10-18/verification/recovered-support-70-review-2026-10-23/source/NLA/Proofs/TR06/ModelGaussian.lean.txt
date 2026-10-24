import NLA.Proofs.TR06.ModelCone
import NLA.Proofs.TR06.ModelMeasure
import NLA.Proofs.TR06.HomogeneousGaussianMean

/-! Instantiation of the proved Hausdorff-cone integration theorem with the
actual tensor smooth locus and actual angular slope. Only the literal annular
geometric bounds and the separately required full-measure theorem remain. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem expectedDimension_gt_one (hr : 1 < r) : 1 < NLA.TR06.expectedDimension d n r := by
  have h : r ≤ r * (1 + ∑ j : Fin d, (n j - 1)) := Nat.le_mul_of_pos_right r (by omega)
  exact hr.trans_le h

theorem smoothVolume_eq_tensorVolume
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    (Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r)).restrict
      (NLA.TR06.smoothRegularSet d n r) = NLA.TR06.tensorVolume d n r := by
  have heq := Measure.restrict_eq_self_of_ae_mem hfull
  rw [NLA.TR06.tensorVolume,Measure.restrict_restrict_of_subset
    NLA.TR06.smoothRegularSet_subset_identifiable] at heq
  exact heq

theorem smooth_gaussianNormalizer_eq_normalization
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    (∫⁻ A in NLA.TR06.smoothRegularSet d n r,
      HomogeneousGaussian.gaussian A
        ∂Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r)) =
      NLA.TR06.normalization d n r := by
  rw [smoothVolume_eq_tensorVolume hfull]
  unfold NLA.TR06.normalization NLA.TR06.unnormalizedInput
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rfl

theorem smooth_weightedSlope_eq_weightedSlope
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r) :
    (∫⁻ A in NLA.TR06.smoothRegularSet d n r,
      NLA.TR06.angularSlope r A * HomogeneousGaussian.gaussian A
        ∂Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r)) =
      ∫⁻ A, NLA.TR06.angularSlope r A * NLA.TR06.gaussianWeight A
        ∂NLA.TR06.tensorVolume d n r := by
  rw [smoothVolume_eq_tensorVolume hfull]
  rfl

/-- This is a reduction with explicit actual geometric obligations, rather
than a proof of the full target or an assumed analytic model oracle. -/
theorem finiteAngularMean_of_actualAnnularBounds
    (hd : 0 < d) (hr : 1 < r)
    (hfull : ∀ᵐ A ∂NLA.TR06.tensorVolume d n r,
      A ∈ NLA.TR06.smoothRegularSet d n r)
    (hvolpos : 0 < (Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r))
      (HomogeneousGaussian.annulus (NLA.TR06.smoothRegularSet d n r)))
    (hvolfinite : (Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r))
      (HomogeneousGaussian.annulus (NLA.TR06.smoothRegularSet d n r)) < ⊤)
    (hangular : (∫⁻ A in HomogeneousGaussian.annulus (NLA.TR06.smoothRegularSet d n r),
      NLA.TR06.angularSlope r A
        ∂Measure.euclideanHausdorffMeasure (NLA.TR06.expectedDimension d n r)) < ⊤) :
    NLA.Statements.TR06.FiniteAngularMean n r := by
  have hcone : HomogeneousGaussian.PositiveCone (NLA.TR06.smoothRegularSet d n r) :=
    fun t ht A => pos_smul_mem_smoothRegular_iff hd t ht A
  have hhom : ∀ t : ℝ, 0 < t → ∀ A ∈ NLA.TR06.smoothRegularSet d n r,
      NLA.TR06.angularSlope r (t • A) =
        (ENNReal.ofReal t)⁻¹ * NLA.TR06.angularSlope r A := by
    intro t ht A _
    rw [angularSlope_pos_smul hd t ht A,div_eq_mul_inv,mul_comm]
  have hpos := HomogeneousGaussian.gaussian_normalizer_pos
    (NLA.TR06.expectedDimension d n r) hvolpos
  have hfinite := HomogeneousGaussian.gaussian_normalizer_lt_top
    (by have := expectedDimension_gt_one (d := d) (n := n) hr; omega)
    measurableSet_smoothRegular hcone (zero_not_mem_smoothRegular (by omega)) hvolfinite
  have hnum := HomogeneousGaussian.gaussian_numerator_lt_top (expectedDimension_gt_one hr)
    measurableSet_smoothRegular hcone (zero_not_mem_smoothRegular (by omega))
    (NLA.TR06.angularSlope r) hhom hangular
  rw [smooth_gaussianNormalizer_eq_normalization hfull] at hpos hfinite
  rw [smooth_weightedSlope_eq_weightedSlope hfull] at hnum
  exact finiteAngularMean_of_weightedSlope ⟨0,hd⟩ hfull hpos hfinite hnum

#assert_trust kernel expectedDimension_gt_one
#assert_trust kernel smoothVolume_eq_tensorVolume
#assert_trust kernel smooth_gaussianNormalizer_eq_normalization
#assert_trust kernel smooth_weightedSlope_eq_weightedSlope
#assert_trust kernel finiteAngularMean_of_actualAnnularBounds
#print axioms finiteAngularMean_of_actualAnnularBounds
end NLA.Proofs.TR06.Model
