import ProofProject.BoundedSemigroup
import ProofProject.AveragingWindow
import ProofProject.IntervalOperatorIntegral
import ProofProject.HilbertFourier

/-!
# Averaged Fourier operators for a bounded semigroup

The operator is defined through vector integrals on the compact averaging
window. Its adjoint is the opposite-frequency average of the adjoint
semigroup. Plancherel then controls both energies on arbitrary Hilbert spaces.
-/

noncomputable section

open MeasureTheory Set FourierTransform

namespace ProofProject

universe u

/-- The scalar Fourier kernel on the averaging interval, in Mathlib's convention. -/
def averagingFourierKernel (N ξ s : ℝ) : ℂ :=
  (((Real.sqrt N)⁻¹ : ℝ) : ℂ) * (Real.fourierChar (-(s * ξ)) : ℂ)

lemma averagingFourierKernel_continuous (N ξ : ℝ) :
    Continuous (averagingFourierKernel N ξ) := by
  exact continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_id.mul_const ξ).neg))

@[simp]
lemma norm_averagingFourierKernel (N ξ s : ℝ) :
    ‖averagingFourierKernel N ξ s‖ = (Real.sqrt N)⁻¹ := by
  simp only [averagingFourierKernel, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg N))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma star_averagingFourierKernel (N ξ s : ℝ) :
    star (averagingFourierKernel N ξ s) = averagingFourierKernel N (-ξ) s := by
  have hc : star (((Real.sqrt N)⁻¹ : ℝ) : ℂ) = (((Real.sqrt N)⁻¹ : ℝ) : ℂ) := by simp
  rw [averagingFourierKernel, star_mul, hc, Circle.star_addChar]
  simp only [averagingFourierKernel, mul_neg, neg_neg]
  exact mul_comm _ _

namespace BoundedSemigroup

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The zero-extended normalized orbit to which classical Plancherel applies. -/
def averagingOrbit (S : BoundedSemigroup M H) (N : ℝ) (x : H) (s : ℝ) : H :=
  averagingWindow N s • S.op s x

lemma averagingInterval_nonneg {N s : ℝ} (hN : 0 < N)
    (hs : s ∈ Icc (N / 2) (3 * N / 2)) : 0 ≤ s := by linarith [hs.1]

lemma averagingInterval_continuous (S : BoundedSemigroup M H) {N : ℝ}
    (hN : 0 < N) (x : H) :
    ContinuousOn (fun s => S.op s x) (Icc (N / 2) (3 * N / 2)) :=
  (S.strong_continuous x).mono fun _ hs => averagingInterval_nonneg hN hs

lemma averagingInterval_bound (S : BoundedSemigroup M H) {N : ℝ}
    (hN : 0 < N) : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖S.op s‖ ≤ M :=
  fun s hs => S.bound s (averagingInterval_nonneg hN hs)

/-- Strong integral construction: no operator-valued Bochner integral is used. -/
def averagedFourierOperator (S : BoundedSemigroup M H) (N : ℝ) (hN : 0 < N)
    (ξ : ℝ) : H →L[ℂ] H :=
  intervalOperatorIntegral S.op (averagingFourierKernel N ξ) (N / 2) (3 * N / 2) M
    (averagingFourierKernel_continuous N ξ).continuousOn
    (S.averagingInterval_continuous hN) S.bound_nonneg (S.averagingInterval_bound hN)

lemma averagingInterval_apply_bound (S : BoundedSemigroup M H) {N : ℝ}
    (hN : 0 < N) (x : H) :
    ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖S.op s x‖ ≤ M * ‖x‖ := by
  intro s hs
  exact ((S.op s).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (S.averagingInterval_bound hN s hs) (norm_nonneg x))

lemma averagingOrbit_integrable (S : BoundedSemigroup M H) {N : ℝ}
    (hN : 0 < N) (x : H) : Integrable (S.averagingOrbit N x) :=
  averagingWindow_smul_integrable (S.averagingInterval_continuous hN x)
    (S.averagingInterval_apply_bound hN x)

lemma averagingOrbit_memLp (S : BoundedSemigroup M H) {N : ℝ}
    (hN : 0 < N) (x : H) : MemLp (S.averagingOrbit N x) 2 :=
  averagingWindow_smul_memLp (mul_nonneg S.bound_nonneg (norm_nonneg x))
    (S.averagingInterval_continuous hN x) (S.averagingInterval_apply_bound hN x)

lemma averagingOrbit_energy_le (S : BoundedSemigroup M H) {N : ℝ}
    (hN : 0 < N) (x : H) :
    (∫ s, ‖S.averagingOrbit N x s‖ ^ 2) ≤ M ^ 2 * ‖x‖ ^ 2 := by
  simpa only [averagingOrbit, mul_pow] using averagingWindow_smul_integral_norm_sq_le hN
    (mul_nonneg S.bound_nonneg (norm_nonneg x))
    (S.averagingInterval_continuous hN x) (S.averagingInterval_apply_bound hN x)

@[simp]
theorem averagedFourierOperator_apply (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (ξ : ℝ) (x : H) :
    S.averagedFourierOperator N hN ξ x =
      ∫ s in Icc (N / 2) (3 * N / 2), averagingFourierKernel N ξ s • S.op s x := rfl

/-- The actual vector integral equals the classical Fourier transform of the
normalized zero-extended orbit, at every frequency. -/
theorem averagedFourierOperator_eq_fourier (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (ξ : ℝ) (x : H) :
    S.averagedFourierOperator N hN ξ x = 𝓕 (S.averagingOrbit N x) ξ := by
  rw [averagedFourierOperator_apply, Real.fourier_real_eq]
  have heq : (fun s : ℝ => Real.fourierChar (-(s * ξ)) • S.averagingOrbit N x s) =
      (Icc (N / 2) (3 * N / 2)).indicator
        (fun s => averagingFourierKernel N ξ s • S.op s x) := by
    funext s
    by_cases hs : s ∈ Icc (N / 2) (3 * N / 2)
    · simp only [averagingOrbit, averagingWindow_of_mem hs, indicator_of_mem hs,
        averagingFourierKernel, Circle.smul_def, mul_smul,
        ← RCLike.real_smul_eq_coe_smul (K := ℂ)]
      exact smul_comm (Real.fourierChar (-(s * ξ)) : ℂ) ((Real.sqrt N)⁻¹ : ℝ) (S.op s x)
    · simp only [averagingOrbit, averagingWindow_of_not_mem hs, zero_smul, smul_zero,
        indicator_of_notMem hs]
  rw [heq, integral_indicator measurableSet_Icc]

/-- The elementary norm bound is uniform over the Fourier frequency. -/
theorem norm_averagedFourierOperator_le (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (ξ : ℝ) : ‖S.averagedFourierOperator N hN ξ‖ ≤ M * Real.sqrt N := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg S.bound_nonneg (Real.sqrt_nonneg N))
  intro x
  rw [averagedFourierOperator_eq_fourier]
  calc
    ‖𝓕 (S.averagingOrbit N x) ξ‖ ≤ ∫ s, ‖S.averagingOrbit N x s‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
        (innerₗ ℝ) (S.averagingOrbit N x) ξ
    _ ≤ (M * ‖x‖) * Real.sqrt N :=
      averagingWindow_smul_integral_norm_le hN
        (S.averagingInterval_continuous hN x) (S.averagingInterval_apply_bound hN x)
    _ = (M * Real.sqrt N) * ‖x‖ := by ring

/-- The adjoint average uses exactly the opposite Fourier frequency. -/
theorem averagedFourierOperator_adjoint (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (ξ : ℝ) :
    star (S.averagedFourierOperator N hN ξ) = S.adjoint.averagedFourierOperator N hN (-ξ) := by
  ext y
  rw [averagedFourierOperator_apply]
  change (intervalOperatorIntegral S.op (averagingFourierKernel N ξ)
    (N / 2) (3 * N / 2) M
    (averagingFourierKernel_continuous N ξ).continuousOn
    (S.averagingInterval_continuous hN) S.bound_nonneg (S.averagingInterval_bound hN)).adjoint y = _
  rw [intervalOperatorIntegral_adjoint_apply]
  · simp only [star_averagingFourierKernel, adjoint_op]
  · intro z
    exact (S.adjoint_strong_continuous z).mono fun _ hs => averagingInterval_nonneg hN hs

/-- The original strong integral over the whole real line, with its zero
extension explicit in the window. -/
theorem averagedFourierOperator_apply_integral (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (ξ : ℝ) (x : H) :
    S.averagedFourierOperator N hN ξ x = ∫ s,
      (Real.fourierChar (-(s * ξ)) : ℂ) • (averagingWindow N s • S.op s x) := by
  rw [averagedFourierOperator_eq_fourier, Real.fourier_real_eq]
  simp only [averagingOrbit, Circle.smul_def]

/-- The conjugated phase has the positive sign in the adjoint vector integral. -/
theorem averagedFourierOperator_adjoint_apply_integral (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (ξ : ℝ) (y : H) :
    star (S.averagedFourierOperator N hN ξ) y = ∫ s,
      (Real.fourierChar (s * ξ) : ℂ) • (averagingWindow N s • star (S.op s) y) := by
  rw [averagedFourierOperator_adjoint, averagedFourierOperator_apply_integral]
  simp only [adjoint_op, mul_neg, neg_neg]

/-- The squared norm is integrable before applying the energy estimate. -/
theorem averagedFourierOperator_integrable_energy (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (x : H) :
    Integrable (fun ξ => ‖S.averagedFourierOperator N hN ξ x‖ ^ 2) := by
  simp only [averagedFourierOperator_eq_fourier]
  exact classicalFourier_integrable_norm_sq (S.averagingOrbit_integrable hN x)
    (S.averagingOrbit_memLp hN x)

theorem averagedFourierOperator_energy_le (S : BoundedSemigroup M H) (N : ℝ)
    (hN : 0 < N) (x : H) :
    (∫ ξ, ‖S.averagedFourierOperator N hN ξ x‖ ^ 2) ≤ M ^ 2 * ‖x‖ ^ 2 := by
  simp only [averagedFourierOperator_eq_fourier]
  rw [classicalFourier_integral_norm_sq (S.averagingOrbit_integrable hN x)
    (S.averagingOrbit_memLp hN x)]
  exact S.averagingOrbit_energy_le hN x

theorem averagedFourierOperator_adjoint_integrable_energy (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (y : H) :
    Integrable (fun ξ => ‖star (S.averagedFourierOperator N hN ξ) y‖ ^ 2) := by
  simp only [averagedFourierOperator_adjoint]
  exact (S.adjoint.averagedFourierOperator_integrable_energy N hN y).comp_neg

theorem averagedFourierOperator_adjoint_energy_le (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (y : H) :
    (∫ ξ, ‖star (S.averagedFourierOperator N hN ξ) y‖ ^ 2) ≤ M ^ 2 * ‖y‖ ^ 2 := by
  simp only [averagedFourierOperator_adjoint]
  have hreflect := integral_neg_eq_self
    (fun ξ : ℝ => ‖S.adjoint.averagedFourierOperator N hN ξ y‖ ^ 2) volume
  exact hreflect.trans_le (S.adjoint.averagedFourierOperator_energy_le N hN y)

end BoundedSemigroup

end ProofProject
