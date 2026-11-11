import NLA.Proofs.RE06.GaussianMomentRows

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment

def joinedGramEntry {d p : ℕ} (x : ((Fin d × Fin p) → ℝ) × (Fin p → ℝ)) : ℝ :=
  (finRowStack x.2 (entryMatrix x.1) *
    (finRowStack x.2 (entryMatrix x.1)).transpose)⁻¹ 0 0

theorem joinedGramEntry_measurable (d p : ℕ) :
    Measurable (joinedGramEntry (d := d) (p := p)) := by
  have hm : Measurable (fun x : ((Fin d × Fin p) → ℝ) × (Fin p → ℝ) =>
      finRowStack x.2 (entryMatrix x.1)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    refine Fin.cases ?_ (fun k => ?_) i
    · exact (measurable_pi_apply j).comp measurable_snd
    · exact (measurable_pi_apply (k,j)).comp measurable_fst
  have hG := Pseudo.measurable_matrix_mul hm (Pseudo.measurable_matrix_transpose hm)
  have hi := (Pseudo.measurable_nonsing_inverse (d + 1)).comp hG
  exact (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp hi)

theorem joinedGramEntry_inner_integrable (d p : ℕ) (hdp : d + 2 < p) :
    ∀ᵐ x : (Fin d × Fin p) → ℝ ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1),
      Integrable (fun z : Fin p → ℝ => joinedGramEntry (x,z))
        (Measure.pi (fun _ : Fin p => gaussianReal 0 1)) := by
  filter_upwards [gaussian_gram_det_ne_zero_ae d p (by omega)] with x hx
  simpa only [joinedGramEntry, fin_inverse_gram_first_entry] using
    inverse_gram_first_entry_integrable (entryMatrix x) hx hdp

theorem joinedGramEntry_inner_integral (d p : ℕ) (hdp : d + 2 < p) :
    ∀ᵐ x : (Fin d × Fin p) → ℝ ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1),
      (∫ z : Fin p → ℝ, joinedGramEntry (x,z)
        ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) =
          1 / ((p : ℝ) - (d : ℝ) - 2) := by
  filter_upwards [gaussian_gram_det_ne_zero_ae d p (by omega)] with x hx
  simpa only [joinedGramEntry, fin_inverse_gram_first_entry] using
    inverse_gram_first_entry_integral (entryMatrix x) hx hdp

theorem joinedGramEntry_inner_norm_integral (d p : ℕ) (hdp : d + 2 < p) :
    ∀ᵐ x : (Fin d × Fin p) → ℝ ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1),
      (∫ z : Fin p → ℝ, ‖joinedGramEntry (x,z)‖
        ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) =
          1 / ((p : ℝ) - (d : ℝ) - 2) := by
  filter_upwards [gaussian_gram_det_ne_zero_ae d p (by omega)] with x hx
  have he := inverse_gram_first_entry_ae (entryMatrix x) hx (by omega)
  calc
    _ = ∫ z : Fin p → ℝ, (rowSchur z (entryMatrix x))⁻¹
        ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      dsimp only [joinedGramEntry]
      rw [fin_inverse_gram_first_entry, hz, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (rowSchur_nonneg z _ hx))]
    _ = _ := rowSchur_inverse_integral (entryMatrix x) hx hdp

theorem joinedGramEntry_integrable (d p : ℕ) (hdp : d + 2 < p) :
    Integrable (joinedGramEntry (d := d) (p := p))
      ((Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin p => gaussianReal 0 1))) := by
  apply (integrable_prod_iff (joinedGramEntry_measurable d p).aestronglyMeasurable).mpr
  refine ⟨joinedGramEntry_inner_integrable d p hdp, ?_⟩
  have he : (fun x => ∫ z : Fin p → ℝ, ‖joinedGramEntry (x,z)‖
      ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) =ᵐ[
        Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)]
      (fun _ => 1 / ((p : ℝ) - (d : ℝ) - 2)) := joinedGramEntry_inner_norm_integral d p hdp
  exact (integrable_const _).congr he.symm

theorem joinedGramEntry_integral (d p : ℕ) (hdp : d + 2 < p) :
    (∫ x, joinedGramEntry (d := d) (p := p) x
      ∂((Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin p => gaussianReal 0 1)))) =
          1 / ((p : ℝ) - (d : ℝ) - 2) := by
  rw [integral_prod _ (joinedGramEntry_integrable d p hdp)]
  rw [integral_congr_ae (joinedGramEntry_inner_integral d p hdp)]
  simp

end NLA.Proofs.RE06.GaussianMoment
