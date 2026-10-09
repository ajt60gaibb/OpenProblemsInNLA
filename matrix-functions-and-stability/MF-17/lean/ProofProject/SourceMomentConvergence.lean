import ProofProject.SourceMomentDefs

/-! Dominated convergence for the finite positive-power moments. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ProofProject

/-- Angular monomials have unit norm, so the same majorant works for every
moment. All convergence and domination assumptions are explicitly a.e. -/
theorem sourceRadialMoment_tendsto {F : ℂ → ℂ} {α : ℝ}
    (hα : α < 1) (hF : Measurable F)
    (hlim : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      Tendsto (fun n : ℕ => F ((sourceRadius n : ℂ) * sourceCircle θ)) atTop
        (𝓝 (F (sourceCircle θ))))
    (hbound : ∀ n : ℕ, ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖F ((sourceRadius n : ℂ) * sourceCircle θ)‖ ≤ sourceRadialMajorant α θ)
    (k : ℕ) :
    Tendsto (fun n => sourceRadialMoment F (sourceRadius n) k) atTop
      (𝓝 (sourceAngularMoment F k)) := by
  unfold sourceRadialMoment sourceAngularMoment
  apply tendsto_integral_of_dominated_convergence (sourceRadialMajorant α)
  · intro n
    exact ((hF.comp (measurable_const.mul measurable_sourceCircle)).mul
      (measurable_sourceCircle.pow_const k)).aestronglyMeasurable
  · exact sourceRadialMajorant_integrable hα
  · intro n
    filter_upwards [hbound n] with θ hθ
    simpa only [norm_mul, norm_pow, norm_sourceCircle, one_pow, mul_one] using hθ
  · filter_upwards [hlim] with θ hθ
    exact hθ.mul_const (sourceCircle θ ^ k)

/-- The same integrable majorant also proves existence of each boundary
moment before it is evaluated. -/
theorem sourceAngularMoment_integrable_of_bound {F : ℂ → ℂ} {α : ℝ}
    (hα : α < 1) (hF : Measurable F)
    (hbound : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖F (sourceCircle θ)‖ ≤ sourceRadialMajorant α θ) (k : ℕ) :
    IntegrableOn (fun θ => F (sourceCircle θ) * sourceCircle θ ^ k)
      (Set.Icc (-Real.pi) Real.pi) := by
  apply (sourceRadialMajorant_integrable hα).mono'
    (((hF.comp measurable_sourceCircle).mul
      (measurable_sourceCircle.pow_const k)).aestronglyMeasurable)
  filter_upwards [hbound] with θ hθ
  change ‖F (sourceCircle θ) * sourceCircle θ ^ k‖ ≤ sourceRadialMajorant α θ
  simpa only [norm_mul, norm_pow, norm_sourceCircle, one_pow, mul_one] using hθ

end ProofProject
