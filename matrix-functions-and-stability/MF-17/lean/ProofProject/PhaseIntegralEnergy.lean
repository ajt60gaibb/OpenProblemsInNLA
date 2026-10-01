import ProofProject.PhaseDeficit

/-!
# Integral energy from the phase margin

All integrals use the given measure without normalization. Orthogonality is
the vanishing integral of `conj A * B`, consistent with the first-conjugate
complex inner product.
-/

noncomputable section

open MeasureTheory Filter
open scoped ComplexConjugate

namespace ProofProject

/-- The pointwise square expansion before the cross term is integrated. -/
lemma phase_scalar_square_identity (m : ℝ) (a b g : ℂ) :
    ‖g * a + b‖ ^ 2 - m ^ 2 * ‖a‖ ^ 2 =
      ‖b + (g - (m : ℂ)) * a‖ ^ 2 +
        (2 * m * (g.re - m)) * ‖a‖ ^ 2 + 2 * m * (star a * b).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A nonnegative margin bounds both itself and the displaced phase by one. -/
lemma phase_scalar_margin_bounds (m : ℝ) {g : ℂ} (hg : ‖g‖ = 1)
    (hδ : 0 ≤ 2 * m * (g.re - m)) :
    2 * m * (g.re - m) ≤ 1 ∧ ‖g - (m : ℂ)‖ ^ 2 ≤ 1 := by
  have hgsq : g.re * g.re + g.im * g.im = 1 := by
    calc
      _ = Complex.normSq g := rfl
      _ = ‖g‖ ^ 2 := Complex.normSq_eq_norm_sq g
      _ = 1 := by rw [hg]; norm_num
  have hid : ‖g - (m : ℂ)‖ ^ 2 + 2 * m * (g.re - m) = 1 - m ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  constructor <;> nlinarith [sq_nonneg ‖g - (m : ℂ)‖, sq_nonneg m]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The unnormalized projection deficit for the actual scalar functions. -/
def phaseIntegralDeficit (μ : Measure Ω) (M : ℝ) (A B g : Ω → ℂ) : ℝ :=
  M ^ 2 * (∫ x, ‖g x * A x + B x‖ ^ 2 ∂μ) - ∫ x, ‖A x‖ ^ 2 ∂μ

lemma memLp_mul_unit_phase {μ : Measure Ω} {A g : Ω → ℂ}
    (hA : MemLp A 2 μ) (hg : Measurable g) (hunit : ∀ᵐ x ∂μ, ‖g x‖ = 1) :
    MemLp (fun x => g x * A x) 2 μ := by
  apply hA.congr_norm (hg.aestronglyMeasurable.mul hA.aestronglyMeasurable)
  filter_upwards [hunit] with x hx
  change ‖A x‖ = ‖g x * A x‖
  simp only [norm_mul, hx, one_mul]

lemma integrable_bounded_weight_sq {μ : Measure Ω} {δ : Ω → ℝ} {A : Ω → ℂ}
    (hδ : Measurable δ) (hδbounds : ∀ᵐ x ∂μ, 0 ≤ δ x ∧ δ x ≤ 1)
    (hA : MemLp A 2 μ) : Integrable (fun x => δ x * ‖A x‖ ^ 2) μ := by
  apply hA.norm.integrable_sq.mono'
    (hδ.aestronglyMeasurable.mul (hA.aestronglyMeasurable.norm.pow 2))
  filter_upwards [hδbounds] with x hx
  change ‖δ x * ‖A x‖ ^ 2‖ ≤ ‖A x‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1 (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) hx.2

/-- Orthogonality removes the sole cross term in the scalar square identity. -/
theorem phase_integral_identity {μ : Measure Ω} {M : ℝ} (hM : 0 < M)
    {A B g : Ω → ℂ} {δ : Ω → ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hg : Measurable g)
    (hunit : ∀ᵐ x ∂μ, ‖g x‖ = 1) (hδ : Measurable δ)
    (hmargin : ∀ᵐ x ∂μ, δ x = 2 * M⁻¹ * ((g x).re - M⁻¹))
    (hδnonneg : ∀ᵐ x ∂μ, 0 ≤ δ x)
    (horth : (∫ x, star (A x) * B x ∂μ) = 0) :
    phaseIntegralDeficit μ M A B g / M ^ 2 =
      (∫ x, ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2 ∂μ) +
        ∫ x, δ x * ‖A x‖ ^ 2 ∂μ := by
  have hδbounds : ∀ᵐ x ∂μ, 0 ≤ δ x ∧ δ x ≤ 1 := by
    filter_upwards [hunit, hmargin, hδnonneg] with x hu hm hn
    exact ⟨hn, hm.symm ▸ (phase_scalar_margin_bounds M⁻¹ hu (hm ▸ hn)).1⟩
  have hGA := memLp_mul_unit_phase hA hg hunit
  have hP : Integrable (fun x => ‖g x * A x + B x‖ ^ 2) μ := by
    simpa only [Pi.add_apply] using (hGA.add hB).norm.integrable_sq
  have hQ' := (hB.add (hGA.sub (hA.const_mul (M⁻¹ : ℂ)))).norm.integrable_sq
  have hQ : Integrable (fun x => ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2) μ := by
    simpa only [Pi.add_apply, Pi.sub_apply, sub_mul] using hQ'
  have hAi := hA.norm.integrable_sq
  have hδAi := integrable_bounded_weight_sq hδ hδbounds hA
  have hcross : Integrable (fun x => star (A x) * B x) μ := by
    exact memLp_one_iff_integrable.mp (hB.mul' hA.star)
  have hid : (fun x => ‖g x * A x + B x‖ ^ 2 - M⁻¹ ^ 2 * ‖A x‖ ^ 2) =ᵐ[μ]
      (fun x => ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2 + δ x * ‖A x‖ ^ 2 +
        (2 * M⁻¹) * (star (A x) * B x).re) := by
    filter_upwards [hmargin] with x hx
    rw [hx]
    simpa only [Complex.ofReal_inv] using phase_scalar_square_identity M⁻¹ (A x) (B x) (g x)
  have hQδ : Integrable
      (fun x => ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2 + δ x * ‖A x‖ ^ 2) μ :=
    hQ.add hδAi
  have hcrossre : Integrable (fun x => (star (A x) * B x).re) μ := hcross.re
  have hcrossint : (∫ x, (star (A x) * B x).re ∂μ) = 0 := by
    calc
      _ = (∫ x, star (A x) * B x ∂μ).re := integral_re hcross
      _ = 0 := by rw [horth]; rfl
  have h := integral_congr_ae hid
  rw [integral_sub hP (hAi.const_mul _), integral_const_mul,
    integral_add hQδ (hcrossre.const_mul _), integral_add hQ hδAi,
    integral_const_mul, hcrossint] at h
  simp only [mul_zero, add_zero] at h
  unfold phaseIntegralDeficit
  convert h using 1
  field_simp [hM.ne']

/-- The weighted energies needed for boundary coefficient extraction. The
constants `1`, `3`, and `6` are independent of the functions and the measure. -/
theorem phase_integral_energy_bounds {μ : Measure Ω} {M : ℝ} (hM : 1 < M)
    {A B g : Ω → ℂ} {δ : Ω → ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hg : Measurable g)
    (hunit : ∀ᵐ x ∂μ, ‖g x‖ = 1) (hδ : Measurable δ)
    (hmargin : ∀ᵐ x ∂μ, δ x = 2 * M⁻¹ * ((g x).re - M⁻¹))
    (hδnonneg : ∀ᵐ x ∂μ, 0 ≤ δ x)
    (horth : (∫ x, star (A x) * B x ∂μ) = 0) :
    Integrable (fun x => δ x * ‖A x‖ ^ 2) μ ∧
    Integrable (fun x => δ x * ‖B x‖ ^ 2) μ ∧
    Integrable (fun x => δ x * ‖A x + B x‖ ^ 2) μ ∧
    (∫ x, δ x * ‖A x‖ ^ 2 ∂μ) ≤ phaseIntegralDeficit μ M A B g / M ^ 2 ∧
    (∫ x, δ x * ‖A x‖ ^ 2 ∂μ) + (∫ x, δ x * ‖B x‖ ^ 2 ∂μ) ≤
      3 * (phaseIntegralDeficit μ M A B g / M ^ 2) ∧
    (∫ x, δ x * ‖A x + B x‖ ^ 2 ∂μ) ≤
      6 * (phaseIntegralDeficit μ M A B g / M ^ 2) := by
  have hbounds : ∀ᵐ x ∂μ,
      (0 ≤ δ x ∧ δ x ≤ 1) ∧ ‖g x - (M⁻¹ : ℂ)‖ ^ 2 ≤ 1 := by
    filter_upwards [hunit, hmargin, hδnonneg] with x hu hm hn
    have hp := phase_scalar_margin_bounds M⁻¹ hu (hm ▸ hn)
    exact ⟨⟨hn, hm.symm ▸ hp.1⟩, by simpa only [Complex.ofReal_inv] using hp.2⟩
  have hδbounds := hbounds.mono fun _ hx => hx.1
  have hδAi := integrable_bounded_weight_sq hδ hδbounds hA
  have hδBi := integrable_bounded_weight_sq hδ hδbounds hB
  have hδABi : Integrable (fun x => δ x * ‖A x + B x‖ ^ 2) μ := by
    simpa only [Pi.add_apply] using integrable_bounded_weight_sq hδ hδbounds (hA.add hB)
  have hGA := memLp_mul_unit_phase hA hg hunit
  have hQ' := (hB.add (hGA.sub (hA.const_mul (M⁻¹ : ℂ)))).norm.integrable_sq
  have hQ : Integrable (fun x => ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2) μ := by
    simpa only [Pi.add_apply, Pi.sub_apply, sub_mul] using hQ'
  have hid := phase_integral_identity (by linarith : 0 < M)
    hA hB hg hunit hδ hmargin hδnonneg horth
  have hQnonneg : 0 ≤ ∫ x, ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hA_bound : (∫ x, δ x * ‖A x‖ ^ 2 ∂μ) ≤ phaseIntegralDeficit μ M A B g / M ^ 2 := by
    rw [hid]
    exact le_add_of_nonneg_left hQnonneg
  have hpoint : ∀ᵐ x ∂μ, δ x * ‖B x‖ ^ 2 ≤
      2 * ‖B x + (g x - (M⁻¹ : ℂ)) * A x‖ ^ 2 + 2 * (δ x * ‖A x‖ ^ 2) := by
    filter_upwards [hbounds] with x hx
    let q := B x + (g x - (M⁻¹ : ℂ)) * A x
    let r := (g x - (M⁻¹ : ℂ)) * A x
    have hb : ‖B x‖ ≤ ‖q‖ + ‖r‖ := by
      simpa only [q, r, add_sub_cancel_right] using norm_sub_le q r
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hr : ‖r‖ ^ 2 ≤ ‖A x‖ ^ 2 := by
      dsimp [r]
      rw [norm_mul, mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hx.2
    have hnorm : ‖B x‖ ^ 2 ≤ 2 * ‖q‖ ^ 2 + 2 * ‖A x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖q‖ - ‖r‖)]
    have hs := mul_le_mul_of_nonneg_left hnorm hx.1.1
    have hqδ : δ x * ‖q‖ ^ 2 ≤ ‖q‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hx.1.2
    change δ x * ‖B x‖ ^ 2 ≤ 2 * ‖q‖ ^ 2 + 2 * (δ x * ‖A x‖ ^ 2)
    nlinarith
  have hB_bound := integral_mono_ae hδBi ((hQ.const_mul 2).add (hδAi.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hB_bound
  rw [integral_add (hQ.const_mul 2) (hδAi.const_mul 2), integral_const_mul,
    integral_const_mul] at hB_bound
  have hsum : (∫ x, δ x * ‖A x‖ ^ 2 ∂μ) + (∫ x, δ x * ‖B x‖ ^ 2 ∂μ) ≤
      3 * (phaseIntegralDeficit μ M A B g / M ^ 2) := by
    rw [hid]
    linarith
  have hABpoint : ∀ᵐ x ∂μ, δ x * ‖A x + B x‖ ^ 2 ≤
      2 * (δ x * ‖A x‖ ^ 2) + 2 * (δ x * ‖B x‖ ^ 2) := by
    filter_upwards [hδnonneg] with x hx
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A x) (B x)) 2
    have hh : ‖A x + B x‖ ^ 2 ≤ 2 * ‖A x‖ ^ 2 + 2 * ‖B x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A x‖ - ‖B x‖)]
    have hm := mul_le_mul_of_nonneg_left hh hx
    nlinarith
  have hAB := integral_mono_ae hδABi ((hδAi.const_mul 2).add (hδBi.const_mul 2)) hABpoint
  simp only [Pi.add_apply] at hAB
  rw [integral_add (hδAi.const_mul 2) (hδBi.const_mul 2), integral_const_mul,
    integral_const_mul] at hAB
  exact ⟨hδAi, hδBi, hδABi, hA_bound, hsum, by linarith⟩

/-- A denominator-free form for the final weighted boundary estimate. -/
theorem phase_integral_energy_coarse {μ : Measure Ω} {M : ℝ} (hM : 1 < M)
    {A B g : Ω → ℂ} {δ : Ω → ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hg : Measurable g)
    (hunit : ∀ᵐ x ∂μ, ‖g x‖ = 1) (hδ : Measurable δ)
    (hmargin : ∀ᵐ x ∂μ, δ x = 2 * M⁻¹ * ((g x).re - M⁻¹))
    (hδnonneg : ∀ᵐ x ∂μ, 0 ≤ δ x)
    (horth : (∫ x, star (A x) * B x ∂μ) = 0) :
    0 ≤ phaseIntegralDeficit μ M A B g ∧
    Integrable (fun x => δ x * ‖A x‖ ^ 2) μ ∧
    Integrable (fun x => δ x * ‖A x + B x‖ ^ 2) μ ∧
    (∫ x, δ x * ‖A x‖ ^ 2 ∂μ) ≤ phaseIntegralDeficit μ M A B g ∧
    (∫ x, δ x * ‖A x + B x‖ ^ 2 ∂μ) ≤ 6 * phaseIntegralDeficit μ M A B g := by
  obtain ⟨hAi, _, hABi, hA_bound, _, hAB_bound⟩ :=
    phase_integral_energy_bounds hM hA hB hg hunit hδ hmargin hδnonneg horth
  have hA_nonneg : 0 ≤ ∫ x, δ x * ‖A x‖ ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hδnonneg] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hMpos : 0 < M ^ 2 := by positivity
  have hE : 0 ≤ phaseIntegralDeficit μ M A B g := by
    simpa only [zero_mul] using (le_div_iff₀ hMpos).mp (hA_nonneg.trans hA_bound)
  have hdiv : phaseIntegralDeficit μ M A B g / M ^ 2 ≤ phaseIntegralDeficit μ M A B g :=
    div_le_self hE (by nlinarith : 1 ≤ M ^ 2)
  exact ⟨hE, hAi, hABi, hA_bound.trans hdiv,
    hAB_bound.trans (mul_le_mul_of_nonneg_left hdiv (by norm_num))⟩

end ProofProject
