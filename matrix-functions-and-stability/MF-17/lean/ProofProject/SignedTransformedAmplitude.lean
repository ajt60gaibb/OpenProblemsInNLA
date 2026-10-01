import ProofProject.PowerAmplitude
import ProofProject.OscillatoryKernel

/-!
# Signed derivative and primitive amplitudes

The two transformations are the actual amplitudes used with `exp (2 σ i √u)`.
Their global identities use vanishing below a positive threshold to remove all
singular behavior at zero. The primitive identity requires `σ = ±1`.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ProofProject

def signedPrimitiveAmplitude (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) : ℂ :=
  (-Complex.I * (σ : ℂ)) * powerAmplitude (1 / 2) a u

def signedDerivativeAmplitude (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) : ℂ :=
  deriv a u + (Complex.I * (σ : ℂ)) * powerAmplitude (-1 / 2) a u

theorem signedPrimitiveAmplitude_eq_zero_of_lt (σ : ℝ) {a : ℝ → ℂ} {δ u : ℝ}
    (hlower : ∀ v < δ, a v = 0) (hu : u < δ) :
    signedPrimitiveAmplitude σ a u = 0 := by
  simp only [signedPrimitiveAmplitude, powerAmplitude_eq_zero (hlower u hu), mul_zero]

theorem signedPrimitiveAmplitude_eq_zero_of_gt (σ : ℝ) {a : ℝ → ℂ} {δ u : ℝ}
    (hupper : ∀ v, δ < v → a v = 0) (hu : δ < u) :
    signedPrimitiveAmplitude σ a u = 0 := by
  simp only [signedPrimitiveAmplitude, powerAmplitude_eq_zero (hupper u hu), mul_zero]

theorem signedDerivativeAmplitude_eq_zero_of_lt (σ : ℝ) {a : ℝ → ℂ} {δ u : ℝ}
    (hlower : ∀ v < δ, a v = 0) (hu : u < δ) :
    signedDerivativeAmplitude σ a u = 0 := by
  have hd : deriv a u = 0 := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_eq_zero_of_lower_support hlower hu 1
  simp only [signedDerivativeAmplitude, hd, powerAmplitude_eq_zero (hlower u hu),
    mul_zero, add_zero]

theorem signedDerivativeAmplitude_eq_zero_of_gt (σ : ℝ) {a : ℝ → ℂ} {δ u : ℝ}
    (hupper : ∀ v, δ < v → a v = 0) (hu : δ < u) :
    signedDerivativeAmplitude σ a u = 0 := by
  have hd : deriv a u = 0 := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_eq_zero_of_upper_support hupper hu 1
  simp only [signedDerivativeAmplitude, hd, powerAmplitude_eq_zero (hupper u hu),
    mul_zero, add_zero]

theorem signedPrimitiveAmplitude_contDiff (σ : ℝ) {a : ℝ → ℂ} {δ : ℝ}
    (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hlower : ∀ u < δ, a u = 0) :
    ContDiff ℝ ∞ (signedPrimitiveAmplitude σ a) :=
  contDiff_const.mul (powerAmplitude_contDiff (1 / 2) ha hδ hlower)

theorem signedDerivativeAmplitude_contDiff (σ : ℝ) {a : ℝ → ℂ} {δ : ℝ}
    (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hlower : ∀ u < δ, a u = 0) :
    ContDiff ℝ ∞ (signedDerivativeAmplitude σ a) :=
  (contDiff_infty_iff_deriv.mp ha).2.add
    (contDiff_const.mul (powerAmplitude_contDiff (-1 / 2) ha hδ hlower))

theorem signedPrimitiveAmplitude_hasCompactSupport (σ : ℝ) {a : ℝ → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (signedPrimitiveAmplitude σ a) := by
  apply ha.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro u hu ha0
  exact hu (by simp only [signedPrimitiveAmplitude, powerAmplitude_eq_zero ha0, mul_zero])

theorem signedDerivativeAmplitude_hasCompactSupport (σ : ℝ) {a : ℝ → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (signedDerivativeAmplitude σ a) := by
  let f : ℝ → ℂ := fun u => (Complex.I * (σ : ℂ)) * powerAmplitude (-1 / 2) a u
  have hf : HasCompactSupport f := by
    apply ha.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro u hu ha0
    exact hu (by simp only [f, powerAmplitude_eq_zero ha0, mul_zero])
  simpa only [signedDerivativeAmplitude, f, Pi.add_apply] using! ha.deriv.add hf

/-- Constant multiplication commutes with every iterated derivative. -/
theorem iteratedDeriv_signedPrimitiveAmplitude (σ : ℝ) (a : ℝ → ℂ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (signedPrimitiveAmplitude σ a) u =
      (-Complex.I * (σ : ℂ)) * iteratedDeriv n (powerAmplitude (1 / 2) a) u := by
  exact iteratedDeriv_const_mul_field _ _

/-- The derivative amplitude's iterated derivatives, on the positive half-line. -/
theorem iteratedDeriv_signedDerivativeAmplitude (σ : ℝ) {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv n (signedDerivativeAmplitude σ a) u =
      iteratedDeriv (n + 1) a u +
        (Complex.I * (σ : ℂ)) * iteratedDeriv n (powerAmplitude (-1 / 2) a) u := by
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hpow : ContDiffAt ℝ n (powerAmplitude (-1 / 2) a) u :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp u
      (Real.contDiffAt_rpow_const_of_ne hu.ne')).mul (ha.contDiffAt.of_le hn)
  change iteratedDeriv n (fun v => deriv a v +
    (Complex.I * (σ : ℂ)) * powerAmplitude (-1 / 2) a v) u = _
  rw [iteratedDeriv_fun_add ((contDiff_infty_iff_deriv.mp ha).2.contDiffAt.of_le hn)
    (contDiffAt_const.mul hpow), iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']

/-- Direct differentiation of the signed kernel at a positive argument. -/
theorem hasDerivAt_oscillatoryKernel_pos (σ : ℝ) {a : ℝ → ℂ} {u : ℝ}
    (ha : DifferentiableAt ℝ a u) (hu : 0 < u) :
    HasDerivAt (oscillatoryKernel σ a)
      (oscillatoryKernel σ (signedDerivativeAmplitude σ a) u) u := by
  have hs := (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hu.ne')).const_mul
    (σ * 2)
  have hd : HasDerivAt (fun v : ℝ => σ * 2 * Real.sqrt v)
      (σ * u ^ (-1 / 2 : ℝ)) u := by
    simp only [← Real.sqrt_eq_rpow] at hs
    convert! hs using 1
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by ring]
    ring
  have he := (hd.ofReal_comp.mul_const Complex.I).cexp
  convert! ha.hasDerivAt.mul he using 1
  simp only [oscillatoryKernel, signedDerivativeAmplitude, powerAmplitude,
    Complex.ofReal_mul]
  ring

/-- Global derivative identity: near zero all participating amplitudes vanish. -/
theorem deriv_oscillatoryKernel_eq_signedDerivativeAmplitude (σ : ℝ)
    {a : ℝ → ℂ} {δ : ℝ} (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ)
    (hlower : ∀ u < δ, a u = 0) :
    deriv (oscillatoryKernel σ a) = oscillatoryKernel σ (signedDerivativeAmplitude σ a) := by
  funext u
  by_cases hu : 0 < u
  · exact (hasDerivAt_oscillatoryKernel_pos σ ((contDiff_infty_iff_deriv.mp ha).1 u) hu).deriv
  · have hud : u < δ := lt_of_le_of_lt (le_of_not_gt hu) hδ
    have hkzero : deriv (oscillatoryKernel σ a) u = 0 := by
      simpa only [iteratedDeriv_one] using iteratedDeriv_eq_zero_of_lower_support
        (a := oscillatoryKernel σ a)
        (fun v hv => (oscillatoryKernel_eq_zero_iff σ a v).mpr (hlower v hv)) hud 1
    rw [hkzero]
    exact ((oscillatoryKernel_eq_zero_iff σ _ u).mpr
      (signedDerivativeAmplitude_eq_zero_of_lt σ hlower hud)).symm

/-- The primitive multiplier cancels the derivative of the phase exactly for
the two source signs. The singular point is covered by the lower support. -/
theorem signedDerivativeAmplitude_primitive (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {a : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ u < δ, a u = 0) (u : ℝ) :
    signedDerivativeAmplitude σ (signedPrimitiveAmplitude σ a) u =
      deriv (signedPrimitiveAmplitude σ a) u + a u := by
  by_cases hu : 0 < u
  · have hpow : u ^ (-1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hu]
      norm_num
    have hp : ((u ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hpow, Complex.ofReal_one]
    have hphase : (Complex.I * (σ : ℂ)) * (-Complex.I * (σ : ℂ)) = 1 := by
      rcases hσ with rfl | rfl <;> norm_num [Complex.I_sq]
    simp only [signedDerivativeAmplitude, signedPrimitiveAmplitude, powerAmplitude]
    congr 1
    calc
      _ = ((Complex.I * (σ : ℂ)) * (-Complex.I * (σ : ℂ))) *
          (((u ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * a u := by ring
      _ = _ := by rw [hphase, hp, one_mul, one_mul]
  · have ha0 := hlower u (lt_of_le_of_lt (le_of_not_gt hu) hδ)
    simp only [signedDerivativeAmplitude, signedPrimitiveAmplitude, powerAmplitude,
      ha0, mul_zero, add_zero]

/-- The source's exact primitive-and-remainder identity for either sign. -/
theorem oscillatoryKernel_eq_deriv_primitive_sub (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {a : ℝ → ℂ} {δ : ℝ} (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ)
    (hlower : ∀ u < δ, a u = 0) :
    oscillatoryKernel σ a = deriv (oscillatoryKernel σ (signedPrimitiveAmplitude σ a)) -
      oscillatoryKernel σ (deriv (signedPrimitiveAmplitude σ a)) := by
  rw [deriv_oscillatoryKernel_eq_signedDerivativeAmplitude σ
    (signedPrimitiveAmplitude_contDiff σ ha hδ hlower) hδ
    (fun u hu => signedPrimitiveAmplitude_eq_zero_of_lt σ hlower hu)]
  funext u
  simp only [Pi.sub_apply, oscillatoryKernel, signedDerivativeAmplitude_primitive σ hσ hδ hlower u]
  ring

end ProofProject
