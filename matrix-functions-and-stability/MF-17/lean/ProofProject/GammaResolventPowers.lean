import ProofProject.GammaConvolution

/-!
# Gamma kernels realize powers of the normalized resolvent average

The scalar convolution identity and the nonnegative-time support turn the
actual strong kernel integrals into operator powers. Their normalized mass
gives a bound by `M`, uniformly in the positive power and rate.
-/

noncomputable section

open MeasureTheory

namespace ProofProject.BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The Gamma kernel of shape `n + 1` is the actual `(n + 1)`st resolvent
power, with no separately supplied resolvent or power representation. -/
theorem resolventAverage_pow_succ_eq_kernelOperator (S : BoundedSemigroup M H)
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    S.resolventAverage r hr ^ (n + 1) =
      S.kernelOperator (gammaKernel n r) (gammaKernel_integrable n hr) := by
  induction n with
  | zero => simp only [zero_add, pow_one, gammaKernel_zero, resolventAverage]
  | succ n ih =>
      rw [pow_succ', ih]
      have h := S.kernelOperator_convolution (gammaKernel_integrable 0 hr)
        (gammaKernel_integrable n hr)
        (fun s hs => gammaKernel_of_nonpos 0 r hs.le)
        (fun s hs => gammaKernel_of_nonpos n r hs.le)
      calc
        _ = (S.kernelOperator (gammaKernel 0 r) (gammaKernel_integrable 0 hr)).comp
            (S.kernelOperator (gammaKernel n r) (gammaKernel_integrable n hr)) := by
          simp only [gammaKernel_zero, resolventAverage]
          rfl
        _ = S.kernelOperator (kernelConvolution (gammaKernel 0 r) (gammaKernel n r))
            (kernelConvolution_integrable (gammaKernel_integrable 0 hr)
              (gammaKernel_integrable n hr)) := h.symm
        _ = _ := by
          ext x
          simp only [kernelOperator_apply]
          rw [gammaKernel_convolution_zero_left n hr]

/-- All positive powers retain the original semigroup bound, including on
the zero Hilbert space. -/
theorem resolventAverage_pow_succ_norm_le (S : BoundedSemigroup M H)
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖S.resolventAverage r hr ^ (n + 1)‖ ≤ M := by
  rw [S.resolventAverage_pow_succ_eq_kernelOperator n r hr]
  simpa only [integral_norm_gammaKernel n hr, mul_one] using
    S.kernelOperator_norm_le (gammaKernel n r) (gammaKernel_integrable n hr)

/-- The power integral uses the original orbit; negative times vanish by
the actual Gamma kernel support. -/
theorem resolventAverage_pow_succ_apply (S : BoundedSemigroup M H)
    (n : ℕ) (r : ℝ) (hr : 0 < r) (x : H) :
    (S.resolventAverage r hr ^ (n + 1)) x =
      ∫ s : ℝ, gammaKernel n r s • S.op s x := by
  rw [S.resolventAverage_pow_succ_eq_kernelOperator n r hr]
  exact S.kernelOperator_apply_of_nonneg_support _ _
    (fun s hs => gammaKernel_of_nonpos n r hs.le) x

/-- Integrability of the vector-valued power integral is proved independently
of its displayed value. -/
theorem gammaKernel_orbit_integrable (S : BoundedSemigroup M H)
    (n : ℕ) (r : ℝ) (hr : 0 < r) (x : H) :
    Integrable (fun s : ℝ => gammaKernel n r s • S.op s x) := by
  apply (S.kernelOrbit_integrable (gammaKernel_integrable n hr) x).congr
  filter_upwards [] with s
  by_cases hs : 0 ≤ s
  · simp only [positiveOrbit, max_eq_left hs]
  · simp only [gammaKernel_of_nonpos n r (le_of_not_ge hs), zero_smul]

end ProofProject.BoundedSemigroup
