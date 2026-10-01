import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.Ring

/-!
# Bilinear scalar Fourier reconstruction

An inverse-sign transform of a scalar Schwartz kernel pairs with the forward
transform of any integrable complex function. There is no complex conjugation
in this identity. Smooth compactly supported kernels supply actual Schwartz
functions and therefore integrable inverse transforms. Explicit exponential
formulas use the normalization `exp (±2π i v ξ)` and Lebesgue measure `dξ`.
-/

noncomputable section

namespace ProofProject

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff

/-- The scalar forward transform, with the function written before the phase. -/
theorem scalarFourier_eq_integral_exp (F : ℝ → ℂ) (ξ : ℝ) :
    𝓕 F ξ = ∫ v : ℝ, F v * Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, mul_comm]

/-- The inverse transform has the positive exponential sign. -/
theorem scalarFourierInv_eq_integral_exp (k : ℝ → ℂ) (ξ : ℝ) :
    𝓕⁻ k ξ = ∫ v : ℝ, k v * Complex.exp (((2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [show -2 * Real.pi * v * (-ξ) = 2 * Real.pi * v * ξ by ring,
    smul_eq_mul, mul_comm]

/-- A Schwartz kernel times an integrable complex function is integrable. -/
theorem schwartz_mul_integrable (k : 𝓢(ℝ, ℂ)) {F : ℝ → ℂ} (hF : Integrable F) :
    Integrable (fun v => k v * F v) :=
  hF.bdd_mul k.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => k.norm_le_seminorm ℝ v))

/-- The frequency-side bilinear product is integrable, so the reconstruction
identity is an equality of convergent integrals. -/
theorem schwartz_fourierInv_mul_fourier_integrable (k : 𝓢(ℝ, ℂ))
    {F : ℝ → ℂ} (hF : Integrable F) :
    Integrable (fun ξ => (𝓕⁻ k) ξ * 𝓕 F ξ) := by
  have hc : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF
  apply ((𝓕⁻ k).integrable (μ := volume)).mul_bdd hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) F ξ)

/-- Bilinear reconstruction for a Schwartz kernel and an arbitrary integrable
complex function. The inverse/forward signs cancel with no conjugation. -/
theorem schwartz_fourierInv_mul_fourier_integral (k : 𝓢(ℝ, ℂ))
    {F : ℝ → ℂ} (hF : Integrable F) :
    (∫ ξ : ℝ, (𝓕⁻ k) ξ * 𝓕 F ξ) = ∫ v : ℝ, k v * F v := by
  have h : (∫ v : ℝ, (𝓕 (𝓕⁻ k)) v * F v) =
      ∫ ξ : ℝ, (𝓕⁻ k) ξ * 𝓕 F ξ := by
    simpa only [smul_eq_mul, flip_innerₗ] using!
      VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
        ((𝓕⁻ k).integrable (μ := volume)) hF
  simpa only [fourier_fourierInv_eq] using h.symm

/-- A smooth compactly supported complex kernel has an integrable inverse
Fourier transform. -/
theorem compactSmooth_fourierInv_integrable {k : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hcompact : HasCompactSupport k) :
    Integrable (𝓕⁻ k) := by
  have h := (𝓕⁻ (hcompact.toSchwartzMap hk)).integrable (μ := (volume : Measure ℝ))
  rw [SchwartzMap.fourierInv_coe] at h
  simpa only using! h

/-- Time-side integrability for an actual smooth compact kernel. -/
theorem compactSmooth_mul_integrable {k F : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hcompact : HasCompactSupport k) (hF : Integrable F) :
    Integrable (fun v => k v * F v) := by
  simpa only using! schwartz_mul_integrable (hcompact.toSchwartzMap hk) hF

/-- Frequency-side integrability for an actual smooth compact kernel. -/
theorem compactSmooth_fourierInv_mul_fourier_integrable {k F : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hcompact : HasCompactSupport k) (hF : Integrable F) :
    Integrable (fun ξ => 𝓕⁻ k ξ * 𝓕 F ξ) := by
  simpa only [SchwartzMap.fourierInv_coe] using!
    schwartz_fourierInv_mul_fourier_integrable (hcompact.toSchwartzMap hk) hF

/-- Smooth compact kernels satisfy the bilinear reconstruction identity against
every integrable complex function. -/
theorem compactSmooth_fourierInv_mul_fourier_integral {k F : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hcompact : HasCompactSupport k) (hF : Integrable F) :
    (∫ ξ : ℝ, 𝓕⁻ k ξ * 𝓕 F ξ) = ∫ v : ℝ, k v * F v := by
  simpa only [SchwartzMap.fourierInv_coe] using!
    schwartz_fourierInv_mul_fourier_integral (hcompact.toSchwartzMap hk) hF

/-- The same reconstruction written with the two explicit exponential signs. -/
theorem compactSmooth_scalarFourier_reconstruction {k F : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hcompact : HasCompactSupport k) (hF : Integrable F) :
    (∫ ξ : ℝ,
      (∫ v : ℝ, k v * Complex.exp (((2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)) *
      (∫ v : ℝ, F v * Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I))) =
      ∫ v : ℝ, k v * F v := by
  simpa only [scalarFourierInv_eq_integral_exp, scalarFourier_eq_integral_exp] using
    compactSmooth_fourierInv_mul_fourier_integral hk hcompact hF

end ProofProject
