import NLA.Proofs.RE06.GaussianMomentKernel
import NLA.Proofs.RE06.GaussianMomentFullRank

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment

theorem rowSchur_pos_ae {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d < p) :
    ∀ᵐ z : Fin p → ℝ ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1),
      0 < rowSchur z W := by
  have hq : 0 < kernelDimension W := by rw [kernelDimension_eq W hW]; omega
  have hlaw := coisometry_coordinates_hasLaw (kernelCoordinates W)
    (kernelCoordinates_coisometry W)
  have hm : Measurable (fun x : Fin (kernelDimension W) → ℝ => 0 < normSq x) := by
    apply measurableSet_setOfPred.mp
    apply IsOpen.measurableSet
    apply isOpen_lt continuous_const
    unfold normSq
    fun_prop
  have hh := (hlaw.ae_iff hm).mpr (normSq_pos_ae (kernelDimension W) hq)
  simpa only [← rowSchur_kernel_normSq _ W hW] using hh

theorem rowStack_gram_det_ne_zero_ae {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d < p) :
    ∀ᵐ z : Fin p → ℝ ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1),
      (rowStack z W * (rowStack z W).transpose).det ≠ 0 := by
  filter_upwards [rowSchur_pos_ae W hW hdp] with z hz
  rw [rowStack_gram_det z W hW]
  exact mul_ne_zero hW (ne_of_gt hz)

theorem inverse_gram_first_entry_ae {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d < p) :
    (fun z : Fin p → ℝ =>
      (rowStack z W * (rowStack z W).transpose)⁻¹ (Sum.inl ()) (Sum.inl ()))
      =ᵐ[Measure.pi (fun _ : Fin p => gaussianReal 0 1)]
        (fun z => (rowSchur z W)⁻¹) := by
  filter_upwards [rowStack_gram_det_ne_zero_ae W hW hdp] with z hz
  exact inverse_gram_first_entry z W hW hz

theorem inverse_gram_first_entry_integrable {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d + 2 < p) :
    Integrable (fun z : Fin p → ℝ =>
      (rowStack z W * (rowStack z W).transpose)⁻¹ (Sum.inl ()) (Sum.inl ()))
      (Measure.pi (fun _ : Fin p => gaussianReal 0 1)) :=
  (rowSchur_inverse_integrable W hW hdp).congr
    (inverse_gram_first_entry_ae W hW (by omega)).symm

theorem inverse_gram_first_entry_integral {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d + 2 < p) :
    (∫ z : Fin p → ℝ,
      (rowStack z W * (rowStack z W).transpose)⁻¹ (Sum.inl ()) (Sum.inl ())
        ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) =
          1 / ((p : ℝ) - (d : ℝ) - 2) := by
  rw [integral_congr_ae (inverse_gram_first_entry_ae W hW (by omega))]
  exact rowSchur_inverse_integral W hW hdp

end NLA.Proofs.RE06.GaussianMoment
