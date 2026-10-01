import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Pointwise separation of reciprocal-square-root windows

These estimates use only rationalization and comparisons of positive square
roots. The center parameter is real, so the statements can later be applied
to every integer window without changing the constants.
-/

noncomputable section

namespace ProofProject

open Set

theorem reciprocalSqrt_window_bounds {n t : ℝ} (hn : 2 ≤ n)
    (ht : t ∈ Icc (n - 3 / 2) (n + 3 / 2)) :
    0 < t ∧ t ≤ 2 * n := by
  constructor <;> linarith [ht.1, ht.2]

theorem reciprocalSqrt_window_sqrt_le {n t : ℝ} (hn : 2 ≤ n)
    (ht : t ∈ Icc (n - 3 / 2) (n + 3 / 2)) :
    Real.sqrt t ≤ (3 / 2 : ℝ) * Real.sqrt n := by
  have hn0 : 0 ≤ n := by linarith
  obtain ⟨ht0, htn⟩ := reciprocalSqrt_window_bounds hn ht
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hn0]

/-- Exact rationalization, valid for all positive arguments. -/
theorem abs_reciprocalSqrt_sub {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    |1 / Real.sqrt R - 1 / Real.sqrt t| =
      |R - t| / (Real.sqrt R * Real.sqrt t * (Real.sqrt R + Real.sqrt t)) := by
  have hr := Real.sqrt_pos.mpr hR
  have hs := Real.sqrt_pos.mpr ht
  have heq : 1 / Real.sqrt R - 1 / Real.sqrt t =
      (t - R) / (Real.sqrt R * Real.sqrt t * (Real.sqrt R + Real.sqrt t)) := by
    field_simp [hr.ne', hs.ne', (add_pos hr hs).ne']
    nlinarith [Real.sq_sqrt hR.le, Real.sq_sqrt ht.le]
  rw [heq, abs_div, abs_of_pos (show 0 < Real.sqrt R * Real.sqrt t *
    (Real.sqrt R + Real.sqrt t) by positivity), abs_sub_comm t R]

theorem reciprocalSqrt_denominator_le {n R t : ℝ} (hn : 2 ≤ n)
    (ht : t ∈ Icc (n - 3 / 2) (n + 3 / 2)) (hR : 0 < R) (hRn : R ≤ 4 * n) :
    Real.sqrt R * Real.sqrt t * (Real.sqrt R + Real.sqrt t) ≤
      10 * n * Real.sqrt n := by
  have hn0 : 0 ≤ n := by linarith
  obtain ⟨ht0, htn⟩ := reciprocalSqrt_window_bounds hn ht
  have hs := reciprocalSqrt_window_sqrt_le hn ht
  have hr : Real.sqrt R ≤ 2 * Real.sqrt n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hn0]
  calc
    Real.sqrt R * Real.sqrt t * (Real.sqrt R + Real.sqrt t) =
        R * Real.sqrt t + t * Real.sqrt R := by
      calc
        _ = Real.sqrt R ^ 2 * Real.sqrt t + Real.sqrt t ^ 2 * Real.sqrt R := by ring
        _ = _ := by rw [Real.sq_sqrt hR.le, Real.sq_sqrt ht0.le]
    _ ≤ (4 * n) * ((3 / 2 : ℝ) * Real.sqrt n) + (2 * n) * (2 * Real.sqrt n) := by
      gcongr
    _ = 10 * n * Real.sqrt n := by ring

/-- In the region `R ≤ 4n`, reciprocal-square-root separation controls the
ordinary distance to each point of the window. -/
theorem reciprocalSqrt_separation_near {n R t : ℝ} (hn : 2 ≤ n)
    (ht : t ∈ Icc (n - 3 / 2) (n + 3 / 2)) (hR : 0 < R) (hRn : R ≤ 4 * n) :
    |R - t| / 10 ≤ n * Real.sqrt n * |1 / Real.sqrt R - 1 / Real.sqrt t| := by
  have ht0 := (reciprocalSqrt_window_bounds hn ht).1
  have hden := reciprocalSqrt_denominator_le hn ht hR hRn
  have hr := Real.sqrt_pos.mpr hR
  have hs := Real.sqrt_pos.mpr ht0
  rw [abs_reciprocalSqrt_sub hR ht0, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (abs_nonneg (R - t))]

/-- Beyond `4n`, the reciprocal-square-root window is uniformly separated
at the scale `n`. -/
theorem reciprocalSqrt_separation_far {n R t : ℝ} (hn : 2 ≤ n)
    (ht : t ∈ Icc (n - 3 / 2) (n + 3 / 2)) (hRn : 4 * n < R) :
    n / 6 ≤ n * Real.sqrt n * |1 / Real.sqrt R - 1 / Real.sqrt t| := by
  have hn0 : 0 < n := by linarith
  have hR : 0 < R := by linarith
  have ht0 := (reciprocalSqrt_window_bounds hn ht).1
  have hnroot := Real.sqrt_pos.mpr hn0
  have htroot := Real.sqrt_pos.mpr ht0
  have hRroot := Real.sqrt_pos.mpr hR
  have hs := reciprocalSqrt_window_sqrt_le hn ht
  have hr : 2 * Real.sqrt n ≤ Real.sqrt R := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.sq_sqrt hn0.le]
  have hRinv : 1 / Real.sqrt R ≤ 1 / (2 * Real.sqrt n) :=
    one_div_le_one_div_of_le (by positivity) hr
  have htinv : 1 / ((3 / 2 : ℝ) * Real.sqrt n) ≤ 1 / Real.sqrt t :=
    one_div_le_one_div_of_le htroot hs
  calc
    n / 6 = n * Real.sqrt n *
        (1 / ((3 / 2 : ℝ) * Real.sqrt n) - 1 / (2 * Real.sqrt n)) := by
      field_simp [hnroot.ne']
      <;> ring
    _ ≤ n * Real.sqrt n * (1 / Real.sqrt t - 1 / Real.sqrt R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ ≤ n * Real.sqrt n * |1 / Real.sqrt R - 1 / Real.sqrt t| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [abs_sub_comm (1 / Real.sqrt t) (1 / Real.sqrt R)] using
        le_abs_self (1 / Real.sqrt t - 1 / Real.sqrt R)

/-- Every nonpositive frequency is uniformly separated from the positive
reciprocal-square-root window. -/
theorem reciprocalSqrt_separation_nonpos {n t v : ℝ} (hn : 2 ≤ n)
    (ht : t ∈ Icc (n - 3 / 2) (n + 3 / 2)) (hv : v ≤ 0) :
    n / 2 ≤ n * Real.sqrt n * |v - 1 / Real.sqrt t| := by
  have hn0 : 0 < n := by linarith
  have ht0 := (reciprocalSqrt_window_bounds hn ht).1
  have hnroot := Real.sqrt_pos.mpr hn0
  have htroot := Real.sqrt_pos.mpr ht0
  have hs : Real.sqrt t ≤ 2 * Real.sqrt n :=
    (reciprocalSqrt_window_sqrt_le hn ht).trans (by nlinarith)
  have htinv : 1 / (2 * Real.sqrt n) ≤ 1 / Real.sqrt t :=
    one_div_le_one_div_of_le htroot hs
  calc
    n / 2 = n * Real.sqrt n * (1 / (2 * Real.sqrt n)) := by
      field_simp [hnroot.ne']
    _ ≤ n * Real.sqrt n * (1 / Real.sqrt t - v) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ ≤ n * Real.sqrt n * |v - 1 / Real.sqrt t| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [abs_sub_comm (1 / Real.sqrt t) v] using
        le_abs_self (1 / Real.sqrt t - v)

end ProofProject
