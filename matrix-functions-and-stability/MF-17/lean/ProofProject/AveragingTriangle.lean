import ProofProject.AveragingWindow
import Mathlib.Analysis.Convolution

/-!
# The triangular convolution and its finite translate partition

The convolution of the normalized interval window with itself is the triangle
centered at `2N`, of height one and support contained in `[N, 3N]`.
-/

noncomputable section

namespace ProofProject

open MeasureTheory Set
open scoped Convolution

/-- The actual convolution of the two source averaging windows. -/
def averagingTriangle (N v : ℝ) : ℝ :=
  ∫ s, averagingWindow N s * averagingWindow N (v - s)

theorem averagingTriangle_eq_convolution (N : ℝ) :
    averagingTriangle N = averagingWindow N ⋆ averagingWindow N := rfl

/-- The convolution integrand is constant on the intersection of the two windows. -/
theorem averagingWindow_product_eq_indicator (N v : ℝ) :
    (fun s => averagingWindow N s * averagingWindow N (v - s)) =
      (Icc (max (N / 2) (v - 3 * N / 2))
        (min (3 * N / 2) (v - N / 2))).indicator
          (fun _ => (Real.sqrt N)⁻¹ ^ 2) := by
  funext s
  have hmem : s ∈ Icc (max (N / 2) (v - 3 * N / 2))
      (min (3 * N / 2) (v - N / 2)) ↔
      s ∈ Icc (N / 2) (3 * N / 2) ∧ v - s ∈ Icc (N / 2) (3 * N / 2) := by
    simp only [mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨h₁, by linarith⟩, h₂, by linarith⟩
  by_cases h₁ : s ∈ Icc (N / 2) (3 * N / 2) <;>
    by_cases h₂ : v - s ∈ Icc (N / 2) (3 * N / 2) <;>
    simp [averagingWindow, hmem, h₁, h₂, pow_two]

theorem averagingWindow_product_integrable (N v : ℝ) :
    Integrable (fun s => averagingWindow N s * averagingWindow N (v - s)) := by
  rw [averagingWindow_product_eq_indicator, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp [Real.volume_Icc])

private theorem averagingTriangle_overlap {N : ℝ} (hN : 0 < N) (v : ℝ) :
    averagingTriangle N v =
      max (min (3 * N / 2) (v - N / 2) - max (N / 2) (v - 3 * N / 2)) 0 / N := by
  rw [averagingTriangle, averagingWindow_product_eq_indicator,
    integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
    smul_eq_mul, inv_pow, Real.sq_sqrt hN.le]
  simp only [div_eq_mul_inv]

/-- The exact triangular convolution formula, including both endpoints. -/
theorem averagingTriangle_eq {N : ℝ} (hN : 0 < N) (v : ℝ) :
    averagingTriangle N v = max 0 (1 - |v / N - 2|) := by
  rw [averagingTriangle_overlap hN]
  by_cases hv : v ≤ 2 * N
  · have hdiv : v / N ≤ 2 := (div_le_iff₀ hN).mpr hv
    rw [min_eq_right (by linarith : v - N / 2 ≤ 3 * N / 2),
      max_eq_left (by linarith : v - 3 * N / 2 ≤ N / 2),
      abs_of_nonpos (by linarith : v / N - 2 ≤ 0),
      ← max_div_div_right hN.le, zero_div]
    rw [show v - N / 2 - N / 2 = v - N by ring]
    rw [sub_div, div_self hN.ne', max_comm]
    congr 1
    ring
  · have hdiv : 2 ≤ v / N := (le_div_iff₀ hN).mpr (by linarith)
    rw [min_eq_left (by linarith : 3 * N / 2 ≤ v - N / 2),
      max_eq_right (by linarith : N / 2 ≤ v - 3 * N / 2),
      abs_of_nonneg (by linarith : 0 ≤ v / N - 2),
      ← max_div_div_right hN.le, zero_div]
    rw [show 3 * N / 2 - (v - 3 * N / 2) = 3 * N - v by ring]
    rw [sub_div, mul_div_cancel_right₀ _ hN.ne', max_comm]
    congr 1
    ring

theorem averagingTriangle_nonneg (N v : ℝ) : 0 ≤ averagingTriangle N v :=
  integral_nonneg fun s => mul_nonneg (averagingWindow_nonneg N s)
    (averagingWindow_nonneg N (v - s))

theorem averagingTriangle_le_one {N : ℝ} (hN : 0 < N) (v : ℝ) :
    averagingTriangle N v ≤ 1 := by
  rw [averagingTriangle_eq hN]
  exact max_le (by norm_num) (by linarith [abs_nonneg (v / N - 2)])

theorem averagingTriangle_eq_zero_of_le {N v : ℝ} (hN : 0 < N) (hv : v ≤ N) :
    averagingTriangle N v = 0 := by
  have hdiv : v / N ≤ 1 := (div_le_iff₀ hN).mpr (by simpa using hv)
  rw [averagingTriangle_eq hN, abs_of_nonpos (by linarith : v / N - 2 ≤ 0)]
  exact max_eq_left (by linarith)

theorem averagingTriangle_eq_zero_of_ge {N v : ℝ} (hN : 0 < N) (hv : 3 * N ≤ v) :
    averagingTriangle N v = 0 := by
  have hdiv : 3 ≤ v / N := (le_div_iff₀ hN).mpr hv
  rw [averagingTriangle_eq hN, abs_of_nonneg (by linarith : 0 ≤ v / N - 2)]
  exact max_eq_left (by linarith)

theorem averagingTriangle_support_subset {N : ℝ} (hN : 0 < N) :
    Function.support (averagingTriangle N) ⊆ Icc N (3 * N) := by
  intro v hv
  constructor
  · by_contra h
    exact hv (averagingTriangle_eq_zero_of_le hN (lt_of_not_ge h).le)
  · by_contra h
    exact hv (averagingTriangle_eq_zero_of_ge hN (lt_of_not_ge h).le)

theorem averagingTriangle_continuous {N : ℝ} (hN : 0 < N) :
    Continuous (averagingTriangle N) := by
  have heq : averagingTriangle N = fun v => max 0 (1 - |v / N - 2|) :=
    funext (averagingTriangle_eq hN)
  rw [heq]
  fun_prop

private def unitRamp (x : ℝ) : ℝ := min 1 (max 0 x)

private theorem unitTriangle_eq_ramp_sub (x : ℝ) :
    max 0 (1 - |x - 2|) = unitRamp (x - 1) - unitRamp (x - 2) := by
  unfold unitRamp
  by_cases h₁ : x ≤ 1
  · rw [abs_of_nonpos (by linarith : x - 2 ≤ 0),
      max_eq_left (by linarith : 1 - -(x - 2) ≤ 0),
      max_eq_left (by linarith : x - 1 ≤ 0),
      max_eq_left (by linarith : x - 2 ≤ 0)]
    norm_num
  · by_cases h₂ : x ≤ 2
    · rw [abs_of_nonpos (by linarith : x - 2 ≤ 0),
        max_eq_right (by linarith : 0 ≤ 1 - -(x - 2)),
        max_eq_right (by linarith : 0 ≤ x - 1),
        max_eq_left (by linarith : x - 2 ≤ 0),
        min_eq_right (by linarith : x - 1 ≤ 1)]
      norm_num
      ring
    · by_cases h₃ : x ≤ 3
      · rw [abs_of_nonneg (by linarith : 0 ≤ x - 2),
          max_eq_right (by linarith : 0 ≤ 1 - (x - 2)),
          max_eq_right (by linarith : 0 ≤ x - 1),
          max_eq_right (by linarith : 0 ≤ x - 2),
          min_eq_left (by linarith : 1 ≤ x - 1),
          min_eq_right (by linarith : x - 2 ≤ 1)]
      · rw [abs_of_nonneg (by linarith : 0 ≤ x - 2),
          max_eq_left (by linarith : 1 - (x - 2) ≤ 0),
          max_eq_right (by linarith : 0 ≤ x - 1),
          max_eq_right (by linarith : 0 ≤ x - 2),
          min_eq_left (by linarith : 1 ≤ x - 1),
          min_eq_left (by linarith : 1 ≤ x - 2), sub_self]

private theorem sum_unitTriangle (x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, max 0 (1 - |x - (j : ℝ) - 2|) =
      unitRamp (x - 1) - unitRamp (x - n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, unitTriangle_eq_ramp_sub]
    push_cast
    rw [show x - (n + 1) - 1 = x - n - 2 by ring]
    ring

/-- A finite number of translates already gives the source partition on
the entire interval between the first and last triangle centers. -/
theorem averagingTriangle_sum_range {N u : ℝ} (hN : 0 < N) (n : ℕ)
    (hu : 2 * N ≤ u) (hun : u ≤ ((n : ℝ) + 1) * N) :
    ∑ j ∈ Finset.range n, averagingTriangle N (u - (j : ℝ) * N) = 1 := by
  have hx : 2 ≤ u / N := (le_div_iff₀ hN).mpr hu
  have hxn : u / N ≤ n + 1 := (div_le_iff₀ hN).mpr hun
  simp_rw [averagingTriangle_eq hN, sub_div, mul_div_cancel_right₀ _ hN.ne']
  rw [sum_unitTriangle]
  unfold unitRamp
  rw [max_eq_right (by linarith : 0 ≤ u / N - 1),
    min_eq_left (by linarith : 1 ≤ u / N - 1),
    max_eq_left (by linarith : u / N - n - 1 ≤ 0)]
  norm_num

end ProofProject
