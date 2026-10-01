import ProofProject.AveragingTriangle
import ProofProject.ScalarFourierReconstruction
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Finite triangular reconstruction by smooth scalar windows

The cutoff is equal to one wherever the triangular convolution is nonzero.
Consequently the actual translated scalar windows reconstruct any kernel
supported between the first and last triangle centers.
-/

noncomputable section

namespace ProofProject

open MeasureTheory FourierTransform SchwartzMap Set
open scoped ContDiff

private def triangleCutoffBump : ContDiffBump (2 : ℝ) :=
  ⟨1, 5 / 4, by norm_num, by norm_num⟩

/-- A fixed actual smooth cutoff, equal to one on `[1,3]` and vanishing
outside `(1/2,7/2)`, as in the source argument. -/
def sourceTriangleCutoff (v : ℝ) : ℂ := (triangleCutoffBump v : ℂ)

theorem sourceTriangleCutoff_contDiff : ContDiff ℝ ∞ sourceTriangleCutoff :=
  Complex.ofRealCLM.contDiff.comp triangleCutoffBump.contDiff

theorem sourceTriangleCutoff_hasCompactSupport : HasCompactSupport sourceTriangleCutoff := by
  exact triangleCutoffBump.hasCompactSupport.comp_left (by simp : (0 : ℂ) = 0)

theorem sourceTriangleCutoff_eq_one {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3) :
    sourceTriangleCutoff v = 1 := by
  have hball : v ∈ Metric.closedBall (2 : ℝ) triangleCutoffBump.rIn := by
    change |v - 2| ≤ 1
    exact abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
  simp only [sourceTriangleCutoff, triangleCutoffBump.one_of_mem_closedBall hball,
    Complex.ofReal_one]

theorem sourceTriangleCutoff_support_subset :
    Function.support sourceTriangleCutoff ⊆ Ioo (1 / 2 : ℝ) (7 / 2) := by
  intro v hv
  have hn : triangleCutoffBump v ≠ 0 := by
    simpa only [Function.mem_support, sourceTriangleCutoff, ne_eq,
      Complex.ofReal_eq_zero] using hv
  have hball : v ∈ Metric.ball (2 : ℝ) triangleCutoffBump.rOut := by
    rw [← triangleCutoffBump.support_eq]
    exact hn
  change |v - 2| < 5 / 4 at hball
  have hh := abs_lt.mp hball
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

/-- The closed support lies strictly inside the source's open cutoff interval. -/
theorem sourceTriangleCutoff_tsupport_subset :
    tsupport sourceTriangleCutoff ⊆ Ioo (1 / 2 : ℝ) (7 / 2) := by
  have hs : Function.support sourceTriangleCutoff ⊆ Function.support triangleCutoffBump := by
    intro v hv
    simpa only [Function.mem_support, sourceTriangleCutoff, ne_eq,
      Complex.ofReal_eq_zero] using hv
  have ht : tsupport sourceTriangleCutoff ⊆ tsupport triangleCutoffBump := closure_mono hs
  intro v hv
  have hb := ht hv
  rw [triangleCutoffBump.tsupport_eq] at hb
  change |v - 2| ≤ 5 / 4 at hb
  have hh := abs_le.mp hb
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem sourceTriangleCutoff_norm_le_one (v : ℝ) : ‖sourceTriangleCutoff v‖ ≤ 1 := by
  rw [sourceTriangleCutoff, Complex.norm_real,
    Real.norm_of_nonneg triangleCutoffBump.nonneg]
  exact triangleCutoffBump.le_one

/-- The actual source kernel in the coordinates of the `j`th triangle. -/
def triangularKernelWindow (N : ℝ) (k ζ : ℝ → ℂ) (j : ℕ) (v : ℝ) : ℂ :=
  k (v + (j : ℝ) * N) * ζ (v / N)

theorem triangularKernelWindow_contDiff (N : ℝ) {k ζ : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hζ : ContDiff ℝ ∞ ζ) (j : ℕ) :
    ContDiff ℝ ∞ (triangularKernelWindow N k ζ j) := by
  unfold triangularKernelWindow
  fun_prop

theorem triangularKernelWindow_hasCompactSupport {N : ℝ} (hN : 0 < N)
    (k : ℝ → ℂ) {ζ : ℝ → ℂ} (hζ : HasCompactSupport ζ) (j : ℕ) :
    HasCompactSupport (triangularKernelWindow N k ζ j) := by
  have hc : HasCompactSupport (fun v : ℝ => ζ (v / N)) := by
    simpa only [Homeomorph.coe_mulRight₀, Function.comp_def, div_eq_mul_inv] using
      hζ.comp_homeomorph (Homeomorph.mulRight₀ N⁻¹ (inv_ne_zero hN.ne'))
  exact hc.mul_left

/-- On each triangular support the auxiliary cutoff disappears exactly. -/
theorem triangularKernelWindow_mul_triangle {N : ℝ} (hN : 0 < N)
    (k : ℝ → ℂ) {ζ : ℝ → ℂ} (hζ : ∀ v ∈ Icc (1 : ℝ) 3, ζ v = 1)
    (j : ℕ) (u : ℝ) :
    triangularKernelWindow N k ζ j (u - (j : ℝ) * N) *
        (averagingTriangle N (u - (j : ℝ) * N) : ℂ) =
      k u * (averagingTriangle N (u - (j : ℝ) * N) : ℂ) := by
  by_cases ht : averagingTriangle N (u - (j : ℝ) * N) = 0
  · simp [ht]
  · have hs := averagingTriangle_support_subset hN ht
    have hscaled : (u - (j : ℝ) * N) / N ∈ Icc (1 : ℝ) 3 := by
      constructor
      · exact (le_div_iff₀ hN).mpr (by simpa using hs.1)
      · exact (div_le_iff₀ hN).mpr hs.2
    simp only [triangularKernelWindow, sub_add_cancel, hζ _ hscaled, mul_one]

/-- Exact reconstruction by finitely many source windows. No smoothness is
required for this algebraic identity. -/
theorem triangularKernelWindow_partition {N : ℝ} (hN : 0 < N)
    {k ζ : ℝ → ℂ} (hζ : ∀ v ∈ Icc (1 : ℝ) 3, ζ v = 1) (n : ℕ)
    (hk : ∀ u, u ∉ Icc (2 * N) (((n : ℝ) + 1) * N) → k u = 0) (u : ℝ) :
    ∑ j ∈ Finset.range n,
      triangularKernelWindow N k ζ j (u - (j : ℝ) * N) *
        (averagingTriangle N (u - (j : ℝ) * N) : ℂ) = k u := by
  simp_rw [triangularKernelWindow_mul_triangle hN k hζ]
  rw [← Finset.mul_sum]
  by_cases hu : u ∈ Icc (2 * N) (((n : ℝ) + 1) * N)
  · have hsum := congrArg Complex.ofReal (averagingTriangle_sum_range hN n hu.1 hu.2)
    simp only [Complex.ofReal_sum, Complex.ofReal_one] at hsum
    rw [hsum, mul_one]
  · rw [hk u hu, zero_mul]

/-- The inverse-sign coefficient used in the source Fourier reconstruction. -/
def triangularKernelCoefficient (N : ℝ) (k ζ : ℝ → ℂ) (j : ℕ) : ℝ → ℂ :=
  𝓕⁻ (triangularKernelWindow N k ζ j)

theorem triangularKernelCoefficient_integrable {N : ℝ} (hN : 0 < N)
    {k ζ : ℝ → ℂ} (hk : ContDiff ℝ ∞ k) (hζ : ContDiff ℝ ∞ ζ)
    (hcompact : HasCompactSupport ζ) (j : ℕ) :
    Integrable (triangularKernelCoefficient N k ζ j) :=
  compactSmooth_fourierInv_integrable (triangularKernelWindow_contDiff N hk hζ j)
    (triangularKernelWindow_hasCompactSupport hN k hcompact j)

theorem triangularKernelCoefficient_continuous {N : ℝ} (hN : 0 < N)
    {k ζ : ℝ → ℂ} (hk : ContDiff ℝ ∞ k) (hζ : ContDiff ℝ ∞ ζ)
    (hcompact : HasCompactSupport ζ) (j : ℕ) :
    Continuous (triangularKernelCoefficient N k ζ j) := by
  have h := (𝓕⁻ ((triangularKernelWindow_hasCompactSupport hN k hcompact j).toSchwartzMap
    (triangularKernelWindow_contDiff N hk hζ j))).continuous
  rw [SchwartzMap.fourierInv_coe] at h
  exact h

theorem triangularKernelCoefficient_eq_integral (N : ℝ) (k ζ : ℝ → ℂ) (j : ℕ) (ξ : ℝ) :
    triangularKernelCoefficient N k ζ j ξ =
      ∫ v : ℝ, k (v + (j : ℝ) * N) * ζ (v / N) *
        Complex.exp (((2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) :=
  scalarFourierInv_eq_integral_exp (triangularKernelWindow N k ζ j) ξ

end ProofProject
