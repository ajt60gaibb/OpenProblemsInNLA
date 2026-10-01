import ProofProject.SemigroupKernelOperator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Normalized exponential averages of a bounded semigroup

The scalar kernel has mass and L¹ norm one. Its operator is defined by strong
integration on each vector; operator-norm measurability is never required.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

/-- The normalized positive-half-line exponential kernel. The value at zero is
zero; changing that single value would leave all integrals unchanged. -/
def resolventKernel (r s : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun s => ((r * Real.exp (-r * s) : ℝ) : ℂ)) s

theorem resolventKernel_of_pos (r : ℝ) {s : ℝ} (hs : 0 < s) :
    resolventKernel r s = ((r * Real.exp (-r * s) : ℝ) : ℂ) :=
  indicator_of_mem hs _

@[simp]
theorem resolventKernel_of_nonpos (r : ℝ) {s : ℝ} (hs : s ≤ 0) :
    resolventKernel r s = 0 :=
  indicator_of_notMem (not_lt_of_ge hs) _

theorem resolventKernel_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (resolventKernel r) := by
  change Integrable ((Ioi (0 : ℝ)).indicator
    (fun s => ((r * Real.exp (-r * s) : ℝ) : ℂ)))
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  exact ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hr) 0).const_mul r).ofReal

theorem norm_resolventKernel {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ‖resolventKernel r s‖ =
      (Ioi (0 : ℝ)).indicator (fun s => r * Real.exp (-r * s)) s := by
  by_cases hs : 0 < s
  · rw [resolventKernel_of_pos r hs,
      indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
  · simp only [resolventKernel_of_nonpos r (le_of_not_gt hs), norm_zero,
      indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]

theorem integral_resolventDensity {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in Ioi 0, r * Real.exp (-r * s)) = 1 := by
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hr)]
  simp [hr.ne']

/-- Exact scalar mass of the actual positive-half-line kernel. -/
theorem integral_resolventKernel {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ, resolventKernel r s) = 1 := by
  change (∫ s : ℝ, (Ioi (0 : ℝ)).indicator
    (fun s => ((r * Real.exp (-r * s) : ℝ) : ℂ)) s) = 1
  rw [integral_indicator measurableSet_Ioi, integral_complex_ofReal,
    integral_resolventDensity hr]
  norm_num

/-- Positivity makes the L¹ norm equal to the exact scalar mass. -/
theorem integral_norm_resolventKernel {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ, ‖resolventKernel r s‖) = 1 := by
  simp_rw [norm_resolventKernel hr.le]
  rw [integral_indicator measurableSet_Ioi, integral_resolventDensity hr]

namespace BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The actual normalized exponential average, built from strong vector integrals. -/
def resolventAverage (S : BoundedSemigroup M H) (r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  S.kernelOperator (resolventKernel r) (resolventKernel_integrable hr)

theorem resolventAverage_orbit_integrable (S : BoundedSemigroup M H)
    {r : ℝ} (hr : 0 < r) (x : H) :
    IntegrableOn (fun s : ℝ => ((r * Real.exp (-r * s) : ℝ) : ℂ) • S.op s x)
      (Ioi 0) := by
  have hi := S.kernelOrbit_integrable (resolventKernel_integrable hr) x
  have heq : (fun s => resolventKernel r s • S.positiveOrbit x s) =
      (Ioi (0 : ℝ)).indicator
        (fun s => ((r * Real.exp (-r * s) : ℝ) : ℂ) • S.op s x) := by
    funext s
    by_cases hs : 0 < s
    · simp only [resolventKernel_of_pos r hs,
        indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),
        positiveOrbit, max_eq_left hs.le]
    · simp only [resolventKernel_of_nonpos r (le_of_not_gt hs), zero_smul,
        indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
  rw [heq, integrable_indicator_iff measurableSet_Ioi] at hi
  exact hi

@[simp]
theorem resolventAverage_apply (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) (x : H) :
    S.resolventAverage r hr x =
      ∫ s : ℝ in Ioi 0, ((r * Real.exp (-r * s) : ℝ) : ℂ) • S.op s x := by
  rw [resolventAverage, S.kernelOperator_apply_of_nonneg_support
    (resolventKernel r) (resolventKernel_integrable hr)
    (fun s hs => resolventKernel_of_nonpos r hs.le)]
  calc
    _ = ∫ s : ℝ, (Ioi (0 : ℝ)).indicator
        (fun s => ((r * Real.exp (-r * s) : ℝ) : ℂ) • S.op s x) s := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        exact (indicator_smul_apply_left (Ioi (0 : ℝ))
          (fun s => ((r * Real.exp (-r * s) : ℝ) : ℂ)) (fun s => S.op s x) s).symm
    _ = _ := integral_indicator measurableSet_Ioi

theorem resolventAverage_norm_le (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) : ‖S.resolventAverage r hr‖ ≤ M := by
  simpa only [resolventAverage, integral_norm_resolventKernel hr, mul_one] using
    S.kernelOperator_norm_le (resolventKernel r) (resolventKernel_integrable hr)

/-- Every semigroup operator at nonnegative time commutes with the average. -/
theorem resolventAverage_commutes (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a) :
    (S.op a).comp (S.resolventAverage r hr) =
      (S.resolventAverage r hr).comp (S.op a) :=
  S.kernelOperator_commutes (resolventKernel r) (resolventKernel_integrable hr) ha

end BoundedSemigroup

end ProofProject
