import ProofProject.SourceMomentConvergence
import ProofProject.SourceRadialLimits
import ProofProject.HolomorphicCircleMoments

/-!
# Boundary moments of the exact source factor

The holomorphic radial identities pass to the boundary by dominated convergence.
Only the moments of `ψ` and `ψ²` are needed for the finite polynomial models.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ProofProject

/-- Holomorphic radial moments and an integrable common majorant identify the
boundary moments. This statement includes all hypotheses of boundary passage. -/
theorem sourceAngularMoment_eq_of_radial_bound {F : ℂ → ℂ} {α : ℝ}
    (hα : α < 1) (hF : Measurable F) (hhol : AnalyticOnNhd ℂ F (Metric.ball 0 1))
    (hlim : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      Tendsto (fun n : ℕ => F ((sourceRadius n : ℂ) * sourceCircle θ)) atTop
        (𝓝 (F (sourceCircle θ))))
    (hbound : ∀ n : ℕ, ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖F ((sourceRadius n : ℂ) * sourceCircle θ)‖ ≤ sourceRadialMajorant α θ)
    (k : ℕ) :
    sourceAngularMoment F k = if k = 0 then (2 * Real.pi : ℂ) * F 0 else 0 := by
  have hconv := sourceRadialMoment_tendsto hα hF hlim hbound k
  have heq : (fun n => sourceRadialMoment F (sourceRadius n) k) =
      (fun _ : ℕ => if k = 0 then (2 * Real.pi : ℂ) * F 0 else 0) := by
    funext n
    exact sourceRadialMoment_eq hhol (sourceRadius_pos n) (sourceRadius_lt_one n) k
  rw [heq] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

lemma ae_sourceWeightFactor_radial_majorant {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ)‖ ≤ sourceRadialMajorant α θ ∧
        ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ) ^ 2‖ ≤
          sourceRadialMajorant α θ := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne 0] with θ hθ hθ0
  exact sourceWeightFactor_radial_majorant hα0 hα1 hr0 hr1
    (abs_pos.mpr hθ0) (abs_le.mpr hθ)

/-- All moments of ψ are integrable as actual boundary functions. -/
theorem sourceWeightFactor_moment_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    IntegrableOn (fun θ => sourceWeightFactor α (sourceCircle θ) * sourceCircle θ ^ k)
      (Set.Icc (-Real.pi) Real.pi) := by
  apply sourceAngularMoment_integrable_of_bound hα1 (measurable_sourceWeightFactor α)
  simpa only [Complex.ofReal_one, one_mul] using
    (ae_sourceWeightFactor_radial_majorant hα0 hα1 (r := 1) (by norm_num)
      (by norm_num)).mono (fun _ h => h.1)

/-- All moments of ψ² are integrable as actual boundary functions. -/
theorem sourceWeightFactor_sq_moment_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    IntegrableOn (fun θ => sourceWeightFactor α (sourceCircle θ) ^ 2 * sourceCircle θ ^ k)
      (Set.Icc (-Real.pi) Real.pi) := by
  apply sourceAngularMoment_integrable_of_bound hα1 ((measurable_sourceWeightFactor α).pow_const 2)
  simpa only [Complex.ofReal_one, one_mul] using
    (ae_sourceWeightFactor_radial_majorant hα0 hα1 (r := 1) (by norm_num)
      (by norm_num)).mono (fun _ h => h.2)

/-- The constant moment of ψ is its center value 1, and its positive moments
vanish. The angular integral is unnormalized, so its constant moment is `2π`. -/
theorem sourceAngularMoment_sourceWeightFactor {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    sourceAngularMoment (sourceWeightFactor α) k =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  have hbound : ∀ n : ℕ, ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖sourceWeightFactor α ((sourceRadius n : ℂ) * sourceCircle θ)‖ ≤
        sourceRadialMajorant α θ := fun n =>
    (ae_sourceWeightFactor_radial_majorant hα0 hα1 (sourceRadius_pos n).le
      (sourceRadius_lt_one n).le).mono (fun _ h => h.1)
  simpa only [sourceWeightFactor_zero, mul_one] using
    sourceAngularMoment_eq_of_radial_bound hα1 (measurable_sourceWeightFactor α)
      (analyticOnNhd_sourceWeightFactor α) (ae_tendsto_sourceWeightFactor_radial α) hbound k

/-- The positive moments of the analytic square vanish as well. These are the
moments used for orthogonality of the disjoint polynomial pieces. -/
theorem sourceAngularMoment_sourceWeightFactor_sq {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    sourceAngularMoment (fun z => sourceWeightFactor α z ^ 2) k =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  have hbound : ∀ n : ℕ, ∀ᵐ θ : ℝ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      ‖sourceWeightFactor α ((sourceRadius n : ℂ) * sourceCircle θ) ^ 2‖ ≤
        sourceRadialMajorant α θ := fun n =>
    (ae_sourceWeightFactor_radial_majorant hα0 hα1 (sourceRadius_pos n).le
      (sourceRadius_lt_one n).le).mono (fun _ h => h.2)
  simpa only [sourceWeightFactor_zero, one_pow, mul_one] using
    sourceAngularMoment_eq_of_radial_bound hα1 ((measurable_sourceWeightFactor α).pow_const 2)
      ((analyticOnNhd_sourceWeightFactor α).pow 2)
      (ae_tendsto_sourceWeightFactor_sq_radial α) hbound k

end ProofProject
