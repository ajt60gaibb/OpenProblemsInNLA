import ProofProject.WeightedCauchySchwarz

/-! From weighted energies to a uniform coefficient and correlation bound. -/

noncomputable section

open MeasureTheory

namespace ProofProject

/-- A deliberately nonoptimal positive constant simplifies the final source
boundary estimate. Here `E` is the unnormalized projection deficit. -/
theorem weighted_boundary_estimate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {δ : Ω → ℝ} {F G ψ : Ω → ℂ} {D J E : ℝ} {t b : ℂ}
    (hδ : Measurable δ) (hδpos : ∀ᵐ x ∂μ, 0 < δ x)
    (hF : Measurable F) (hG : Measurable G) (hψ : Measurable ψ)
    (hFE : Integrable (fun x => δ x * ‖F x‖ ^ 2) μ)
    (hGE : Integrable (fun x => δ x * ‖G x‖ ^ 2) μ)
    (hdual0 : Integrable (fun x => 1 / δ x) μ)
    (hdualψ : Integrable (fun x => ‖ψ x‖ ^ 2 / δ x) μ)
    (hJ0 : (∫ x, 1 / δ x ∂μ) ≤ J)
    (hJψ : (∫ x, ‖ψ x‖ ^ 2 / δ x ∂μ) ≤ J)
    (hD : 0 < D) (hJ : 0 ≤ J) (hE : 0 ≤ E)
    (hFbound : (∫ x, δ x * ‖F x‖ ^ 2 ∂μ) ≤ 6 * E)
    (hGbound : (∫ x, δ x * ‖G x‖ ^ 2 ∂μ) ≤ E)
    (ht : (∫ x, F x ∂μ) = (2 * Real.pi : ℂ) * t)
    (hb : (∫ x, G x * star (ψ x) ∂μ) = (D : ℂ) * b) :
    ‖t‖ ^ 2 + ‖b‖ ^ 2 ≤ (1 + J * (6 * D + D⁻¹)) * (E / D) := by
  have hFE0 : 0 ≤ ∫ x, δ x * ‖F x‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hδpos.mono fun x hx => mul_nonneg hx.le (sq_nonneg _))
  have hGE0 : 0 ≤ ∫ x, δ x * ‖G x‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hδpos.mono fun x hx => mul_nonneg hx.le (sq_nonneg _))
  have htbound := (weighted_integral_bound μ hδ hδpos hF hFE hdual0).2
  have hbbound := (weighted_integral_mul_conj_bound μ hδ hδpos hG hψ hGE hdualψ).2
  have htbound' := htbound.trans (mul_le_mul hJ0 hFbound hFE0 hJ)
  have hbbound' := hbbound.trans (mul_le_mul hJψ hGbound hGE0 hJ)
  rw [ht, norm_mul, mul_pow] at htbound'
  rw [hb, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD] at hbbound'
  have hπnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hπnorm] at htbound'
  have htsmall : ‖t‖ ^ 2 ≤ 6 * J * E := by
    have hπ : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have h := mul_le_mul_of_nonneg_right hπ (sq_nonneg ‖t‖)
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right htsmall (sq_nonneg D)
  have hcancel : (1 + J * (6 * D + D⁻¹)) * (E / D) * D ^ 2 =
      E * D + 6 * J * E * D ^ 2 + J * E := by
    field_simp [hD.ne']
    <;> ring
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp
  rw [hcancel]
  nlinarith [mul_nonneg hE hD.le]

end ProofProject
