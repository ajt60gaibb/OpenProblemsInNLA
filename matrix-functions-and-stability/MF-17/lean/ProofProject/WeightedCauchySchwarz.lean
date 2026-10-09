import Mathlib

/-!
# Weighted Cauchy--Schwarz for complex integrals

A positive measurable weight splits the product into two square-integrable
factors. Integrability of the product is proved together with the estimate;
no integrability of the original unweighted function is assumed.
-/

noncomputable section

open MeasureTheory Filter

namespace ProofProject

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The complex integral form of ordinary L² Cauchy--Schwarz. -/
lemma integral_mul_sq_le_L2 (μ : Measure Ω) {f g : Ω → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hholder : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (show MemLp f (ENNReal.ofReal 2) μ by simpa using hf)
      (show MemLp g (ENNReal.ofReal 2) μ by simpa using hg)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hh
  have hbound : ‖∫ x, f x * g x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
      _ ≤ _ := hholder
  have hf0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hg0 : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  simpa only [mul_pow, Real.sq_sqrt hf0, Real.sq_sqrt hg0] using hs

/-- Weighted Cauchy--Schwarz for a complex product, including the derived
integrability of that product. The weight need be positive only almost everywhere. -/
theorem weighted_integral_mul_bound (μ : Measure Ω) {δ : Ω → ℝ} {f g : Ω → ℂ}
    (hδ : Measurable δ) (hδpos : ∀ᵐ x ∂μ, 0 < δ x)
    (hf : Measurable f) (hg : Measurable g)
    (henergy : Integrable (fun x => δ x * ‖f x‖ ^ 2) μ)
    (hdual : Integrable (fun x => ‖g x‖ ^ 2 / δ x) μ) :
    Integrable (fun x => f x * g x) μ ∧
      ‖∫ x, f x * g x ∂μ‖ ^ 2 ≤
        (∫ x, ‖g x‖ ^ 2 / δ x ∂μ) * (∫ x, δ x * ‖f x‖ ^ 2 ∂μ) := by
  let u : Ω → ℂ := fun x => (Real.sqrt (δ x) : ℂ) * f x
  let v : Ω → ℂ := fun x => g x / (Real.sqrt (δ x) : ℂ)
  have hroot : Measurable (fun x => (Real.sqrt (δ x) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hδ.sqrt
  have hu : Measurable u := hroot.mul hf
  have hv : Measurable v := hg.div hroot
  have hueq : (fun x => ‖u x‖ ^ 2) =ᵐ[μ] (fun x => δ x * ‖f x‖ ^ 2) := by
    filter_upwards [hδpos] with x hx
    dsimp [u]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hx.le]
  have hveq : (fun x => ‖v x‖ ^ 2) =ᵐ[μ] (fun x => ‖g x‖ ^ 2 / δ x) := by
    filter_upwards [hδpos] with x hx
    dsimp [v]
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hx.le]
  have huL2 : MemLp u 2 μ := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
    (henergy.congr hueq.symm)
  have hvL2 : MemLp v 2 μ := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
    (hdual.congr hveq.symm)
  have hproduct : (fun x => u x * v x) =ᵐ[μ] (fun x => f x * g x) := by
    filter_upwards [hδpos] with x hx
    have hrootne : (Real.sqrt (δ x) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
    dsimp [u, v]
    field_simp
  have hprodL1 : MemLp (fun x => u x * v x) 1 μ := hvL2.mul' huL2
  refine ⟨(memLp_one_iff_integrable.mp hprodL1).congr hproduct, ?_⟩
  have hcs := integral_mul_sq_le_L2 μ huL2 hvL2
  rw [integral_congr_ae hproduct, integral_congr_ae hueq, integral_congr_ae hveq] at hcs
  simpa only [mul_comm] using hcs

/-- The weighted estimate for a single complex integral, with integrability
following from the two displayed weighted assumptions. -/
theorem weighted_integral_bound (μ : Measure Ω) {δ : Ω → ℝ} {f : Ω → ℂ}
    (hδ : Measurable δ) (hδpos : ∀ᵐ x ∂μ, 0 < δ x) (hf : Measurable f)
    (henergy : Integrable (fun x => δ x * ‖f x‖ ^ 2) μ)
    (hdual : Integrable (fun x => 1 / δ x) μ) :
    Integrable f μ ∧ ‖∫ x, f x ∂μ‖ ^ 2 ≤
      (∫ x, 1 / δ x ∂μ) * (∫ x, δ x * ‖f x‖ ^ 2 ∂μ) := by
  have h := weighted_integral_mul_bound μ hδ hδpos hf
    (show Measurable (fun _ : Ω => (1 : ℂ)) from measurable_const) henergy
    (by simpa only [norm_one, one_pow] using hdual)
  simpa only [mul_one, norm_one, one_pow] using h

/-- The inner-product version used for the coefficient and projection
correlations in the source boundary estimate. -/
theorem weighted_integral_mul_conj_bound (μ : Measure Ω) {δ : Ω → ℝ} {f ψ : Ω → ℂ}
    (hδ : Measurable δ) (hδpos : ∀ᵐ x ∂μ, 0 < δ x)
    (hf : Measurable f) (hψ : Measurable ψ)
    (henergy : Integrable (fun x => δ x * ‖f x‖ ^ 2) μ)
    (hdual : Integrable (fun x => ‖ψ x‖ ^ 2 / δ x) μ) :
    Integrable (fun x => f x * star (ψ x)) μ ∧
      ‖∫ x, f x * star (ψ x) ∂μ‖ ^ 2 ≤
        (∫ x, ‖ψ x‖ ^ 2 / δ x ∂μ) * (∫ x, δ x * ‖f x‖ ^ 2 ∂μ) := by
  simpa only [Function.comp_def, norm_star] using weighted_integral_mul_bound μ hδ hδpos hf (continuous_star.measurable.comp hψ) henergy
    (by simpa only [Function.comp_def, norm_star] using hdual)

end ProofProject
