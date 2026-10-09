import ProofProject.SourcePhaseMargin
import ProofProject.SourceRadialIntegrability
import ProofProject.PhaseQuotientIntegral

/-! Finiteness of the source's reciprocal-margin integral. -/

noncomputable section

open MeasureTheory

namespace ProofProject

lemma measurable_sourcePhaseMargin (α : ℝ) : Measurable (sourcePhaseMargin α) := by
  unfold sourcePhaseMargin sourceBoundaryPhase
  have hm := (measurable_sourceWeightFactor α).comp measurable_sourceCircle
  fun_prop

/-- The exact source boundary factor has the required finite reciprocal-margin
integral. The three exceptional angles are discarded only as null sets. -/
theorem source_margin_quotient_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntegrableOn (fun θ => (1 + ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2) /
      sourcePhaseMargin α θ) (Set.Icc (-Real.pi) Real.pi) := by
  apply integrableOn_phase_quotient (ν := sourceWeightNu α)
    (K := Real.exp (2 * sourceWeightCorrectionBound α) * (2 : ℝ) ^ α * Real.pi ^ α)
    (c := sourcePhaseMarginConstant α) hα0 (sourceWeightNu_add_lt_one hα1)
    (by positivity) (sourcePhaseMarginConstant_pos hα0 hα1)
  · exact (((measurable_sourceWeightFactor α).comp measurable_sourceCircle).norm).pow_const 2
  · exact measurable_sourcePhaseMargin α
  · intro θ _ _
    positivity
  · intro θ hθ0 hθπ
    simpa only [Complex.ofReal_one, one_mul] using
      sourceWeightFactor_radial_norm_sq_le hα0 hα1 (r := 1) (by norm_num)
        (by norm_num) hθ0 hθπ.le
  · intro θ hθ0 hθπ
    exact sourcePhaseMargin_lower_abs hα0 hα1 hθ0 hθπ

theorem source_margin_quotient_intervalIntegrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => (1 + ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2) /
      sourcePhaseMargin α θ) volume (-Real.pi) Real.pi := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr
    (source_margin_quotient_integrable hα0 hα1)

/-- The reciprocal-margin integral at the target's exact exponent is finite. -/
theorem source_margin_quotient_growthExponent {M : ℝ} (hM : 1 < M) :
    IntegrableOn (fun θ =>
      (1 + ‖sourceWeightFactor (growthExponent M) (sourceCircle θ)‖ ^ 2) /
        (2 * (1 / M) *
          ((sourceBoundaryPhase (growthExponent M) θ).re - 1 / M)))
      (Set.Icc (-Real.pi) Real.pi) := by
  simpa only [sourcePhaseMargin_growthExponent M _ hM.le] using
    source_margin_quotient_integrable (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2

end ProofProject
