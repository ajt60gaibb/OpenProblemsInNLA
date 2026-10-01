import Mathlib.Analysis.Fourier.LpSpace

/-!
# Classical Fourier integrals and Hilbert-valued Plancherel

For an integrable, square-integrable Hilbert-valued function, its classical
Bochner Fourier transform agrees almost everywhere with Mathlib's isometry
on `L²`. The identification uses compact smooth test functions and does not
assume that the Hilbert space is separable. Fourier normalization is
`exp (-2 * π * I * s * ξ)` throughout.
-/

noncomputable section

namespace ProofProject

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Classical and `L²` Fourier transforms agree on `L¹ ∩ L²`, with no
separability condition on the Hilbert codomain. -/
theorem classicalFourier_ae_eq_l2 {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2) :
    ((𝓕 (hf2.toLp f) : Lp H 2 volume) : ℝ → H) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf2.toLp f))).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable
  intro g hg hc
  have hgc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hgc.toSchwartzMap hgd
  have htest :
      ∫ x, φ x • (𝓕 (hf2.toLp f) : Lp H 2 volume) x = ∫ x, φ x • 𝓕 f x := by
    calc
      _ = Lp.toTemperedDistribution (𝓕 (hf2.toLp f) : Lp H 2 volume) φ := by
        rw [Lp.toTemperedDistribution_apply]
      _ = 𝓕 ((hf2.toLp f : Lp H 2 volume) : 𝓢'(ℝ, H)) φ := by
        rw [Lp.fourier_toTemperedDistribution_eq]
      _ = ∫ x, (𝓕 φ) x • (hf2.toLp f) x := by
        rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      _ = ∫ x, (𝓕 φ) x • f x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := by
        simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner φ.integrable hf1
  change ∫ x, (g x : ℂ) • (𝓕 (hf2.toLp f) : Lp H 2 volume) x =
    ∫ x, (g x : ℂ) • 𝓕 f x at htest
  simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact htest

/-- The classical Fourier transform of an `L¹ ∩ L²` function is in `L²`. -/
theorem classicalFourier_memLp {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  MemLp.ae_eq (classicalFourier_ae_eq_l2 hf1 hf2) (Lp.memLp (𝓕 (hf2.toLp f)))

/-- The `L²` element represented by the classical transform is the Fourier
isometry applied to the original function. -/
theorem classicalFourier_toLp {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2) :
    (classicalFourier_memLp hf1 hf2).toLp (𝓕 f) = 𝓕 (hf2.toLp f) := by
  apply Lp.ext
  exact (classicalFourier_memLp hf1 hf2).coeFn_toLp.trans
    (classicalFourier_ae_eq_l2 hf1 hf2).symm

/-- Plancherel's norm identity for the classical Hilbert-valued transform. -/
theorem classicalFourier_norm_toLp {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2) :
    ‖(classicalFourier_memLp hf1 hf2).toLp (𝓕 f)‖ = ‖hf2.toLp f‖ := by
  rw [classicalFourier_toLp hf1 hf2, Lp.norm_fourier_eq]

private theorem norm_toLp_sq_eq_integral {f : ℝ → H} (hf : MemLp f 2) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ = RCLike.re (inner ℂ (hf.toLp f) (hf.toLp f)) :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = ∫ x, RCLike.re (inner ℂ ((hf.toLp f) x) ((hf.toLp f) x)) := by
      rw [L2.inner_def, integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

/-- The square norm of the classical Fourier transform is integrable. -/
theorem classicalFourier_integrable_norm_sq {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2) : Integrable (fun ξ => ‖𝓕 f ξ‖ ^ 2) :=
  (classicalFourier_memLp hf1 hf2).norm.integrable_sq

/-- Hilbert-valued Plancherel stated directly as equality of ordinary integrals. -/
theorem classicalFourier_integral_norm_sq {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2) : (∫ ξ, ‖𝓕 f ξ‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  rw [← norm_toLp_sq_eq_integral (classicalFourier_memLp hf1 hf2),
    ← norm_toLp_sq_eq_integral hf2, classicalFourier_norm_toLp hf1 hf2]

end ProofProject
