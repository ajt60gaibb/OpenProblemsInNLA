import ProofProject.SemigroupKernelConvolution
import ProofProject.ResolventAverage
import ProofProject.ResolventKernelIntegration
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Scalar convolution with the normalized exponential kernel

The actual full-line convolution reduces to an interval integral for kernels
supported at nonnegative times. The integration-by-parts boundary contribution
is displayed before it is removed by continuity and negative-time vanishing.
The convolution and its derivative version are integrable under the source's
smooth compact-support assumptions.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace ProofProject

/-- Exponential convolution preserves scalar integrability. -/
theorem kernelConvolution_resolventKernel_integrable {r : ℝ} (hr : 0 < r)
    {k : ℝ → ℂ} (hk : Integrable k) :
    Integrable (kernelConvolution (resolventKernel r) k) :=
  kernelConvolution_integrable (resolventKernel_integrable hr) hk

/-- Reflection of the integration variable puts the exponential on `v-u`. -/
theorem kernelConvolution_resolventKernel_eq_swap (r : ℝ) (k : ℝ → ℂ) (v : ℝ) :
    kernelConvolution (resolventKernel r) k v =
      ∫ u : ℝ, resolventKernel r (v - u) * k u := by
  unfold kernelConvolution
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun s : ℝ => resolventKernel r s * k (v - s)) volume v).symm

/-- The lower support assumption and the exponential's positive support give
the exact finite-interval representation. Endpoint values have measure zero. -/
theorem kernelConvolution_resolventKernel_eq_interval (r : ℝ) {k : ℝ → ℂ}
    (hsupp : ∀ u < 0, k u = 0) {v : ℝ} (hv : 0 ≤ v) :
    kernelConvolution (resolventKernel r) k v =
      (r : ℂ) * ∫ u in (0 : ℝ)..v,
        (Real.exp (-r * (v - u)) : ℂ) * k u := by
  rw [kernelConvolution_resolventKernel_eq_swap]
  calc
    _ = ∫ u : ℝ, (Icc (0 : ℝ) v).indicator
        (fun u => (r : ℂ) * ((Real.exp (-r * (v - u)) : ℂ) * k u)) u := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne v] with u huv
      by_cases hu : u ∈ Icc (0 : ℝ) v
      · rw [indicator_of_mem hu, resolventKernel_of_pos r (by
          have hlt : u < v := lt_of_le_of_ne hu.2 huv
          linarith)]
        simp only [Complex.ofReal_mul, mul_assoc]
      · rw [indicator_of_notMem hu]
        by_cases hu0 : u < 0
        · rw [hsupp u hu0, mul_zero]
        · have hvu : v ≤ u := by
            by_contra h
            exact hu ⟨le_of_not_gt hu0, (lt_of_not_ge h).le⟩
          rw [resolventKernel_of_nonpos r (sub_nonpos.mpr hvu), zero_mul]
    _ = ∫ u in Icc (0 : ℝ) v,
        (r : ℂ) * ((Real.exp (-r * (v - u)) : ℂ) * k u) :=
      integral_indicator measurableSet_Icc
    _ = ∫ u in (0 : ℝ)..v,
        (r : ℂ) * ((Real.exp (-r * (v - u)) : ℂ) * k u) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hv]
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem kernelConvolution_resolventKernel_eq_zero_of_neg (r : ℝ) {k : ℝ → ℂ}
    (hsupp : ∀ u < 0, k u = 0) {v : ℝ} (hv : v < 0) :
    kernelConvolution (resolventKernel r) k v = 0 :=
  kernelConvolution_eq_zero_of_neg (fun _ hs => resolventKernel_of_nonpos r hs.le) hsupp hv

/-- The actual convolution identity with its full lower-end boundary term. -/
theorem kernelConvolution_resolventKernel_deriv_boundary (r : ℝ) {v : ℝ} (hv : 0 ≤ v)
    {k k' : ℝ → ℂ} (hks : ∀ u < 0, k u = 0) (hk's : ∀ u < 0, k' u = 0)
    (hk : ∀ u ∈ Icc 0 v, HasDerivAt k (k' u) u)
    (hk'int : IntervalIntegrable k' volume 0 v) :
    kernelConvolution (resolventKernel r) k' v =
      (r : ℂ) * k v - (r : ℂ) * (Real.exp (-r * v) : ℂ) * k 0 -
        (r : ℂ) * kernelConvolution (resolventKernel r) k v := by
  rw [kernelConvolution_resolventKernel_eq_interval r hk's hv,
    kernelConvolution_resolventKernel_eq_interval r hks hv]
  convert resolventKernel_integration_by_parts r hv hk hk'int using 1
  ring

/-- Continuity and vanishing at all negative times force the value at zero. -/
theorem continuous_kernel_zero_at_zero {k : ℝ → ℂ} (hk : Continuous k)
    (hsupp : ∀ u < 0, k u = 0) : k 0 = 0 := by
  have heq : EqOn k (fun _ => (0 : ℂ)) (Iio (0 : ℝ)) := hsupp
  exact heq.closure hk continuous_const (by simp only [closure_Iio, mem_Iic, le_refl])

/-- The real derivative also vanishes at every negative time. -/
theorem deriv_kernel_zero_of_neg {k : ℝ → ℂ} (hsupp : ∀ u < 0, k u = 0)
    {v : ℝ} (hv : v < 0) : deriv k v = 0 := by
  have heq : k =ᶠ[𝓝 v] (fun _ => (0 : ℂ)) := by
    filter_upwards [gt_mem_nhds hv] with u hu
    exact hsupp u hu
  simpa only [deriv_const] using heq.deriv_eq

/-- The resolvent convolution identity for the source's actual smooth kernel.
The statement is pointwise on the whole real line, including zero and negative
times, and no positivity of the rate is needed for this finite-interval identity. -/
theorem kernelConvolution_resolventKernel_deriv (r : ℝ) {k : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hsupp : ∀ u < 0, k u = 0) (v : ℝ) :
    kernelConvolution (resolventKernel r) (deriv k) v =
      (r : ℂ) * k v - (r : ℂ) * kernelConvolution (resolventKernel r) k v := by
  have hk's : ∀ u < 0, deriv k u = 0 := fun _ hu => deriv_kernel_zero_of_neg hsupp hu
  by_cases hv : 0 ≤ v
  · have hd := (contDiff_infty_iff_deriv.mp hk).1
    have hdc := (contDiff_infty_iff_deriv.mp hk).2.continuous
    have h := kernelConvolution_resolventKernel_deriv_boundary r hv hsupp hk's
      (fun u _ => (hd u).hasDerivAt) (hdc.intervalIntegrable 0 v)
    simpa only [continuous_kernel_zero_at_zero hk.continuous hsupp, mul_zero, sub_zero] using h
  · have hneg : v < 0 := lt_of_not_ge hv
    rw [kernelConvolution_resolventKernel_eq_zero_of_neg r hk's hneg,
      kernelConvolution_resolventKernel_eq_zero_of_neg r hsupp hneg, hsupp v hneg]
    simp

/-- Under smooth compact support, the differentiated convolution is an L¹
function before the operator convolution identity is used. -/
theorem kernelConvolution_resolventKernel_deriv_integrable {r : ℝ} (hr : 0 < r)
    {k : ℝ → ℂ} (hk : ContDiff ℝ ∞ k) (hcompact : HasCompactSupport k) :
    Integrable (kernelConvolution (resolventKernel r) (deriv k)) :=
  kernelConvolution_resolventKernel_integrable hr
    ((contDiff_infty_iff_deriv.mp hk).2.continuous.integrable_of_hasCompactSupport hcompact.deriv)

end ProofProject
