import ProofProject.ScalarFourierReconstruction
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Smooth oscillatory kernels supported away from zero

The actual phase `exp (2 σ i √u)` has unit norm for every real `σ` and `u`.
Multiplying by an amplitude that vanishes below a positive threshold removes
the square-root singularity at zero. Thus a smooth compactly supported
amplitude supplies a globally smooth compact kernel for Fourier reconstruction.
No oscillatory Fourier estimate is asserted here.
-/

noncomputable section

namespace ProofProject

open MeasureTheory FourierTransform
open scoped ContDiff Topology

/-- The complex oscillatory kernel, with either source sign given by `σ = ±1`. -/
def oscillatoryKernel (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) : ℂ :=
  a u * Complex.exp (((σ * 2 * Real.sqrt u : ℝ) : ℂ) * Complex.I)

/-- Reversing the phase by conjugation also conjugates a complex amplitude. -/
theorem oscillatoryKernel_star (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) :
    star (oscillatoryKernel σ a u) =
      oscillatoryKernel (-σ) (fun v => star (a v)) u := by
  simp [oscillatoryKernel, ← Complex.exp_conj, map_ofNat, mul_neg, neg_mul]

/-- The phase has exactly unit norm, including at and below zero. -/
@[simp] theorem oscillatoryKernel_norm (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) :
    ‖oscillatoryKernel σ a u‖ = ‖a u‖ := by
  unfold oscillatoryKernel
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[simp] theorem oscillatoryKernel_eq_zero_iff (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) :
    oscillatoryKernel σ a u = 0 ↔ a u = 0 := by
  simp [oscillatoryKernel, Complex.exp_ne_zero]

/-- Multiplication by this phase preserves the amplitude's exact support. -/
theorem oscillatoryKernel_support (σ : ℝ) (a : ℝ → ℂ) :
    Function.support (oscillatoryKernel σ a) = Function.support a := by
  ext u
  change oscillatoryKernel σ a u ≠ 0 ↔ a u ≠ 0
  exact not_congr (oscillatoryKernel_eq_zero_iff σ a u)

theorem oscillatoryKernel_tsupport (σ : ℝ) (a : ℝ → ℂ) :
    tsupport (oscillatoryKernel σ a) = tsupport a := by
  simp only [tsupport, oscillatoryKernel_support]

theorem oscillatoryKernel_hasCompactSupport (σ : ℝ) {a : ℝ → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (oscillatoryKernel σ a) := by
  simpa only [HasCompactSupport, oscillatoryKernel_tsupport] using ha

/-- The possibly nonsmooth phase remains globally continuous. -/
theorem oscillatoryKernel_continuous (σ : ℝ) {a : ℝ → ℂ}
    (ha : Continuous a) : Continuous (oscillatoryKernel σ a) := by
  unfold oscillatoryKernel
  exact ha.mul (by fun_prop)

/-- An integrable amplitude gives an integrable kernel without additional
support or regularity hypotheses. -/
theorem oscillatoryKernel_integrable (σ : ℝ) {a : ℝ → ℂ}
    (ha : Integrable a) : Integrable (oscillatoryKernel σ a) := by
  have hc : Continuous (fun u : ℝ =>
      Complex.exp (((σ * 2 * Real.sqrt u : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  exact ha.mul_bdd (c := 1) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by
      simp only [Complex.norm_exp_ofReal_mul_I, le_refl]))

/-- Vanishing below a positive threshold removes the only nonsmooth point
of the square-root phase. -/
theorem oscillatoryKernel_contDiff (σ : ℝ) {a : ℝ → ℂ} {δ : ℝ}
    (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hvanish : ∀ u < δ, a u = 0) :
    ContDiff ℝ ∞ (oscillatoryKernel σ a) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · have hsqrt : ContDiffAt ℝ ∞ Real.sqrt u := Real.contDiffAt_sqrt hu.ne'
    have hr : ContDiffAt ℝ ∞ (fun v : ℝ => σ * 2 * Real.sqrt v) u :=
      contDiffAt_const.mul hsqrt
    have hc : ContDiffAt ℝ ∞ (fun v : ℝ => ((σ * 2 * Real.sqrt v : ℝ) : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u hr
    exact ha.contDiffAt.mul ((hc.mul contDiffAt_const).cexp)
  · have huδ : u < δ := lt_of_le_of_lt (le_of_not_gt hu) hδ
    have heq : oscillatoryKernel σ a =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
      filter_upwards [gt_mem_nhds huδ] with v hv
      simp [oscillatoryKernel, hvanish v hv]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The kernel inherits any lower support threshold of its amplitude. -/
theorem oscillatoryKernel_support_subset (σ : ℝ) {a : ℝ → ℂ} {δ : ℝ}
    (hvanish : ∀ u < δ, a u = 0) :
    Function.support (oscillatoryKernel σ a) ⊆ Set.Ici δ := by
  rw [oscillatoryKernel_support]
  intro u hu
  by_contra h
  exact hu (hvanish u (lt_of_not_ge h))

theorem oscillatoryKernel_eq_zero_of_neg (σ : ℝ) {a : ℝ → ℂ} {δ u : ℝ}
    (hδ : 0 < δ) (hvanish : ∀ v < δ, a v = 0) (hu : u < 0) :
    oscillatoryKernel σ a u = 0 := by
  rw [oscillatoryKernel_eq_zero_iff]
  exact hvanish u (hu.trans hδ)

/-- The actual smooth compact oscillatory kernel has an integrable inverse
Fourier transform, as required by the finite reconstruction theorem. -/
theorem oscillatoryKernel_fourierInv_integrable (σ : ℝ) {a : ℝ → ℂ} {δ : ℝ}
    (ha : ContDiff ℝ ∞ a) (hcompact : HasCompactSupport a)
    (hδ : 0 < δ) (hvanish : ∀ u < δ, a u = 0) :
    Integrable (𝓕⁻ (oscillatoryKernel σ a)) :=
  compactSmooth_fourierInv_integrable (oscillatoryKernel_contDiff σ ha hδ hvanish)
    (oscillatoryKernel_hasCompactSupport σ hcompact)

end ProofProject
