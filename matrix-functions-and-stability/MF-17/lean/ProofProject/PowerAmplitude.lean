import ProofProject.DampedPowerDerivatives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Multiplication of a supported complex amplitude by a real power

Differentiation of the raw power is restricted to positive arguments. The
lower support of an amplitude supplies global smoothness of the product.
Finite Leibniz sums give weighted derivative estimates without a loss in the
power of the integration variable.
-/

noncomputable section

open Set Filter Finset
open scoped Topology ContDiff

namespace ProofProject

def powerAmplitude (β : ℝ) (a : ℝ → ℂ) (u : ℝ) : ℂ := (u ^ β : ℝ) * a u

theorem powerAmplitude_eq_zero {β : ℝ} {a : ℝ → ℂ} {u : ℝ} (ha : a u = 0) :
    powerAmplitude β a u = 0 := by simp only [powerAmplitude, ha, mul_zero]

theorem powerAmplitude_support_subset (β : ℝ) (a : ℝ → ℂ) :
    Function.support (powerAmplitude β a) ⊆ Function.support a := by
  intro u hu ha
  exact hu (powerAmplitude_eq_zero ha)

theorem powerAmplitude_hasCompactSupport (β : ℝ) {a : ℝ → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (powerAmplitude β a) :=
  ha.of_isClosed_subset isClosed_closure
    (closure_mono (powerAmplitude_support_subset β a))

theorem powerAmplitude_contDiff (β : ℝ) {a : ℝ → ℂ} {δ : ℝ}
    (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hlower : ∀ u < δ, a u = 0) :
    ContDiff ℝ ∞ (powerAmplitude β a) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u
      (Real.contDiffAt_rpow_const_of_ne hu.ne')).mul ha.contDiffAt
  · have hlow : u < δ := lt_of_le_of_lt (le_of_not_gt hu) hδ
    have heq : powerAmplitude β a =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
      filter_upwards [gt_mem_nhds hlow] with v hv
      exact powerAmplitude_eq_zero (hlower v hv)
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Derivatives vanish on any open half-line where the amplitude vanishes. -/
theorem iteratedDeriv_eq_zero_of_lower_support {a : ℝ → ℂ} {δ u : ℝ}
    (hlower : ∀ v < δ, a v = 0) (hu : u < δ) (n : ℕ) :
    iteratedDeriv n a u = 0 := by
  have heq : a =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact hlower v hv
  rw [heq.iteratedDeriv_eq n]
  simp

theorem iteratedDeriv_eq_zero_of_upper_support {a : ℝ → ℂ} {δ u : ℝ}
    (hupper : ∀ v, δ < v → a v = 0) (hu : δ < u) (n : ℕ) :
    iteratedDeriv n a u = 0 := by
  have heq : a =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact hupper v hv
  rw [heq.iteratedDeriv_eq n]
  simp

theorem powerAmplitude_hasDerivAt (β : ℝ) {a : ℝ → ℂ} {u : ℝ}
    (ha : DifferentiableAt ℝ a u) (hu : 0 < u) :
    HasDerivAt (powerAmplitude β a)
      ((β * u ^ (β - 1) : ℝ) * a u + (u ^ β : ℝ) * deriv a u) u :=
  (Real.hasDerivAt_rpow_const (Or.inl hu.ne')).ofReal_comp.mul ha.hasDerivAt

theorem deriv_powerAmplitude (β : ℝ) {a : ℝ → ℂ} {u : ℝ}
    (ha : DifferentiableAt ℝ a u) (hu : 0 < u) :
    deriv (powerAmplitude β a) u =
      ((β * u ^ (β - 1) : ℝ) * a u + (u ^ β : ℝ) * deriv a u) :=
  (powerAmplitude_hasDerivAt β ha hu).deriv

theorem iteratedDeriv_ofReal_rpow_pos (β : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv n (fun v : ℝ => ((v ^ β : ℝ) : ℂ)) u =
      ((rpowDerivativeCoefficient β n * u ^ (β - n) : ℝ) : ℂ) := by
  induction n generalizing u with
  | zero => simp [rpowDerivativeCoefficient]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun v : ℝ => ((v ^ β : ℝ) : ℂ)) =ᶠ[𝓝 u]
        fun v => ((rpowDerivativeCoefficient β n * v ^ (β - n) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact ih hv
    rw [heq.deriv_eq]
    rw [(((Real.hasDerivAt_rpow_const (p := β - n) (Or.inl hu.ne')).const_mul
      (rpowDerivativeCoefficient β n)).ofReal_comp).deriv]
    congr 1
    simp only [rpowDerivativeCoefficient, prod_range_succ, Nat.cast_add, Nat.cast_one]
    rw [show β - (n : ℝ) - 1 = β - ((n : ℝ) + 1) by ring]
    ring

def powerAmplitudeDerivativeConstant (β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℝ) * |rpowDerivativeCoefficient β i|

theorem powerAmplitudeDerivativeConstant_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ powerAmplitudeDerivativeConstant β n := by
  apply sum_nonneg
  intro i hi
  positivity

/-- The finite Leibniz estimate for multiplication by a real power. -/
theorem norm_iteratedDeriv_powerAmplitude_le (β γ : ℝ) (n : ℕ)
    {a : ℝ → ℂ} {A u : ℝ} (ha : ContDiff ℝ ∞ a) (hA0 : 0 ≤ A) (hu : 0 < u)
    (hA : ∀ j : ℕ, j ≤ n → ‖iteratedDeriv j a u‖ ≤ A * u ^ (γ - j)) :
    ‖iteratedDeriv n (powerAmplitude β a) u‖ ≤
      powerAmplitudeDerivativeConstant β n * A * u ^ (β + γ - n) := by
  have hp : ContDiffAt ℝ n (fun v : ℝ => ((v ^ β : ℝ) : ℂ)) u :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp u
      (Real.contDiffAt_rpow_const_of_ne hu.ne')
  have ha' : ContDiffAt ℝ n a u := ha.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  change ‖iteratedDeriv n ((fun v : ℝ => ((v ^ β : ℝ) : ℂ)) * a) u‖ ≤ _
  rw [iteratedDeriv_mul hp ha']
  calc
    _ ≤ ∑ i ∈ range (n + 1), ‖(n.choose i : ℂ) *
        iteratedDeriv i (fun v : ℝ => ((v ^ β : ℝ) : ℂ)) u *
        iteratedDeriv (n - i) a u‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n + 1),
        ((n.choose i : ℝ) * |rpowDerivativeCoefficient β i|) *
          A * u ^ (β + γ - n) := by
      apply sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
      rw [iteratedDeriv_ofReal_rpow_pos β i hu, norm_mul, norm_mul,
        Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hu.le _)]
      calc
        _ ≤ ((n.choose i : ℝ) * (|rpowDerivativeCoefficient β i| * u ^ (β - i))) *
            (A * u ^ (γ - ((n - i : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hA (n - i) (Nat.sub_le _ _)) (by positivity)
        _ = ((n.choose i : ℝ) * |rpowDerivativeCoefficient β i|) * A *
            (u ^ (β - i) * u ^ (γ - ((n - i : ℕ) : ℝ))) := by ring
        _ = _ := by
          rw [← Real.rpow_add hu]
          congr 2
          rw [Nat.cast_sub hin]
          ring
    _ = _ := by simp only [powerAmplitudeDerivativeConstant, sum_mul]

end ProofProject
