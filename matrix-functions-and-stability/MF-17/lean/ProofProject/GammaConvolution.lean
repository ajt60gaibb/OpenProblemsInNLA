import ProofProject.GammaKernel
import ProofProject.SemigroupKernelConvolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Convolution of normalized gamma kernels

Convolution with the shape-one kernel increments the shape. At each positive
time the scalar integrand is supported on the finite interval between zero
and that time. Combining the exponentials leaves an ordinary polynomial
integral. Values at zero and negative times are checked separately.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

private theorem gammaKernel_convolution_integrand (n : ℕ) (r v s : ℝ) :
    gammaKernel 0 r s * gammaKernel n r (v - s) =
      (Ioo (0 : ℝ) v).indicator
        (fun s => ((r ^ (n + 2) * Real.exp (-r * v) /
          (n.factorial : ℝ) * (v - s) ^ n : ℝ) : ℂ)) s := by
  by_cases hs : s ∈ Ioo (0 : ℝ) v
  · rw [gammaKernel_of_pos 0 r hs.1, gammaKernel_of_pos n r (sub_pos.mpr hs.2),
      indicator_of_mem hs, ← Complex.ofReal_mul]
    congr 1
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    have he : Real.exp (-r * s) * Real.exp (-r * (v - s)) = Real.exp (-r * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = r ^ (n + 2) * (Real.exp (-r * s) * Real.exp (-r * (v - s))) *
          (v - s) ^ n / (n.factorial : ℝ) := by simp only [pow_succ]; ring
      _ = _ := by rw [he]; ring
  · rw [indicator_of_notMem hs]
    by_cases hs0 : s ≤ 0
    · rw [gammaKernel_of_nonpos 0 r hs0, zero_mul]
    · have hvs : v - s ≤ 0 := by
        by_contra h
        exact hs ⟨lt_of_not_ge hs0, sub_pos.mp (lt_of_not_ge h)⟩
      rw [gammaKernel_of_nonpos n r hvs, mul_zero]

/-- The finite-interval convolution identity is valid even for rates for which
the individual full-line kernels are not integrable. -/
theorem gammaKernel_convolution_zero_apply (n : ℕ) (r v : ℝ) :
    kernelConvolution (gammaKernel 0 r) (gammaKernel n r) v = gammaKernel (n + 1) r v := by
  by_cases hv : 0 < v
  · have heq : (fun s => gammaKernel 0 r s * gammaKernel n r (v - s)) =
        (Ioo (0 : ℝ) v).indicator
          (fun s => ((r ^ (n + 2) * Real.exp (-r * v) /
            (n.factorial : ℝ) * (v - s) ^ n : ℝ) : ℂ)) := by
      funext s
      exact gammaKernel_convolution_integrand n r v s
    unfold kernelConvolution
    rw [heq, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hv.le, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ n) v]
    simp only [sub_self, sub_zero, integral_pow, zero_pow (Nat.succ_ne_zero n)]
    rw [gammaKernel_of_pos (n + 1) r hv]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hv0 : v ≤ 0 := le_of_not_gt hv
    rw [gammaKernel_of_nonpos (n + 1) r hv0]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun s => by
      change gammaKernel 0 r s * gammaKernel n r (v - s) = 0
      by_cases hs : s ≤ 0
      · rw [gammaKernel_of_nonpos 0 r hs, zero_mul]
      · rw [gammaKernel_of_nonpos n r (by linarith), mul_zero]

/-- Convolution with the normalized exponential kernel increases the gamma
shape by one. This is literal function equality on the whole real line. -/
theorem gammaKernel_convolution_zero_left (n : ℕ) {r : ℝ} (_hr : 0 < r) :
    kernelConvolution (gammaKernel 0 r) (gammaKernel n r) = gammaKernel (n + 1) r := by
  funext v
  exact gammaKernel_convolution_zero_apply n r v

end ProofProject
