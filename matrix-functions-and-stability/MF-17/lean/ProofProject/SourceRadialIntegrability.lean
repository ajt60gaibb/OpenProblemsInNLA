import ProofProject.SourceRadialBounds
import ProofProject.AngularPowerIntegrals

/-! Integrable majorants for the two functions used in the boundary moments. -/

noncomputable section

open MeasureTheory

namespace ProofProject

lemma measurable_sourceWeightFactor (α : ℝ) : Measurable (sourceWeightFactor α) := by
  unfold sourceWeightFactor sourceCayley
  fun_prop

lemma measurable_sourceCircle : Measurable sourceCircle := by
  unfold sourceCircle
  fun_prop

/-- One integrable majorant works for both `ψ` and `ψ²`, uniformly in the radius. -/
def sourceRadialMajorant (α θ : ℝ) : ℝ :=
  1 + (Real.exp (2 * sourceWeightCorrectionBound α) * (2 : ℝ) ^ α *
    Real.pi ^ α) * |θ| ^ (-α)

lemma sourceRadialMajorant_integrable {α : ℝ} (hα : α < 1) :
    IntegrableOn (sourceRadialMajorant α) (Set.Icc (-Real.pi) Real.pi) := by
  exact (integrableOn_const (s := Set.Icc (-Real.pi) Real.pi) (C := (1 : ℝ))
    (hs := isCompact_Icc.measure_lt_top.ne)).add
    ((integrableOn_Icc_abs_singular_power hα Real.pi_pos).const_mul _)

theorem sourceWeightFactor_radial_majorant {α r θ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hθ0 : 0 < |θ|) (hθπ : |θ| ≤ Real.pi) :
    ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ)‖ ≤ sourceRadialMajorant α θ ∧
      ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ) ^ 2‖ ≤
        sourceRadialMajorant α θ := by
  have h := sourceWeightFactor_radial_norm_sq_le hα0 hα1 hr0 hr1 hθ0 hθπ
  rw [norm_pow]
  unfold sourceRadialMajorant
  constructor
  · nlinarith [sq_nonneg (‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ)‖ - 1 / 2)]
  · linarith

/-- The boundary values and every inner radial circle have integrable `ψ` and
`ψ²`. Values assigned at the singular point do not enter the domination proof. -/
theorem sourceWeightFactor_radial_integrable {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IntegrableOn (fun θ => sourceWeightFactor α ((r : ℂ) * sourceCircle θ))
        (Set.Icc (-Real.pi) Real.pi) ∧
      IntegrableOn (fun θ => sourceWeightFactor α ((r : ℂ) * sourceCircle θ) ^ 2)
        (Set.Icc (-Real.pi) Real.pi) := by
  have hm : Measurable (fun θ => sourceWeightFactor α ((r : ℂ) * sourceCircle θ)) :=
    (measurable_sourceWeightFactor α).comp (measurable_const.mul measurable_sourceCircle)
  have hbound : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ)‖ ≤ sourceRadialMajorant α θ ∧
        ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ) ^ 2‖ ≤
          sourceRadialMajorant α θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (show ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi), θ ≠ 0 from
        ae_iff.mpr (by simp))] with θ hθ hθ0
    exact sourceWeightFactor_radial_majorant hα0 hα1 hr0 hr1
      (abs_pos.mpr hθ0) (abs_le.mpr hθ)
  exact ⟨(sourceRadialMajorant_integrable hα1).mono' hm.aestronglyMeasurable.restrict
      (hbound.mono fun _ h => h.1),
    (sourceRadialMajorant_integrable hα1).mono' (hm.pow_const 2).aestronglyMeasurable.restrict
      (hbound.mono fun _ h => h.2)⟩

/-- In particular the weight used for the Hilbert polynomial norm is integrable. -/
theorem sourceWeightFactor_radial_norm_sq_integrable {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IntegrableOn (fun θ => ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ)‖ ^ 2)
      (Set.Icc (-Real.pi) Real.pi) := by
  simpa only [IntegrableOn, norm_pow] using
    (sourceWeightFactor_radial_integrable hα0 hα1 hr0 hr1).2.norm

end ProofProject
