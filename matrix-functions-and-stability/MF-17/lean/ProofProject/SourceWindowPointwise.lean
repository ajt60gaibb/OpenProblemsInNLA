import ProofProject.SourceFrequencyNormalization
import ProofProject.ReciprocalSqrtSeparation

/-!
# Uniform pointwise gaps for the actual source phase

The reciprocal-square-root estimates hold at every point of the fixed
integration window. The resulting gaps can be inserted directly into the
smoothed window bound, with no minimizer or distance-to-image construction.
-/

noncomputable section

namespace ProofProject

open Set

/-- The positive normalized frequency is the reciprocal square root of
`R = 1 / v²`. -/
theorem reciprocalSqrt_inv_sq {v : ℝ} (hv : 0 < v) :
    1 / Real.sqrt (1 / v ^ 2) = v := by
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq hv.le, one_div_one_div]

/-- The lattice distance to the enlarged center is bounded by the distance
to every point of the actual window. -/
theorem sourceWindow_lattice_distance_le (R : ℝ) (j : ℕ) {w : ℝ}
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    max 0 (|R - ((j : ℝ) + 2)| - 3 / 2) ≤ |R - ((j : ℝ) + w)| := by
  have hshift : |((j : ℝ) + w) - ((j : ℝ) + 2)| ≤ (3 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
  refine max_le (abs_nonneg _) ?_
  have htriangle := abs_sub_le R ((j : ℝ) + w) ((j : ℝ) + 2)
  linarith

/-- Nonpositive normalized frequencies have a gap at least half the center
index throughout the integration window. -/
theorem sourceWindow_phase_gap_nonpos {N : ℝ} (hN : 0 < N) (j : ℕ) (ξ : ℝ)
    (hv : -2 * Real.pi * ξ * Real.sqrt N ≤ 0) (w : ℝ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    sourceWindowScale N j * (((j : ℝ) + 2) / 2) ≤
      |sourceOscillatoryPhaseDeriv N j ξ w| := by
  have hn : (2 : ℝ) ≤ (j : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have ht : (j : ℝ) + w ∈ Icc (((j : ℝ) + 2) - 3 / 2) (((j : ℝ) + 2) + 3 / 2) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  rw [abs_sourceOscillatoryPhaseDeriv_normalized hN j hw]
  exact mul_le_mul_of_nonneg_left (reciprocalSqrt_separation_nonpos hn ht hv)
    (sourceWindowScale_pos hN j).le

/-- For a positive reciprocal-square-root frequency in the near region,
the enlarged lattice distance gives a uniform phase gap. -/
theorem sourceWindow_phase_gap_near {N R : ℝ} (hN : 0 < N) (j : ℕ) (ξ : ℝ)
    (hR : 0 < R) (hv : -2 * Real.pi * ξ * Real.sqrt N = 1 / Real.sqrt R)
    (hRn : R ≤ 4 * ((j : ℝ) + 2)) (w : ℝ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    sourceWindowScale N j * (max 0 (|R - ((j : ℝ) + 2)| - 3 / 2) / 10) ≤
      |sourceOscillatoryPhaseDeriv N j ξ w| := by
  have hn : (2 : ℝ) ≤ (j : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have ht : (j : ℝ) + w ∈ Icc (((j : ℝ) + 2) - 3 / 2) (((j : ℝ) + 2) + 3 / 2) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  rw [abs_sourceOscillatoryPhaseDeriv_normalized hN j hw, hv]
  apply mul_le_mul_of_nonneg_left _ (sourceWindowScale_pos hN j).le
  exact (div_le_div_of_nonneg_right (sourceWindow_lattice_distance_le R j hw)
    (by norm_num : (0 : ℝ) ≤ 10)).trans (reciprocalSqrt_separation_near hn ht hR hRn)

/-- Positive reciprocal-square-root frequencies beyond `4n` have a uniform
gap of at least one sixth of the center index. -/
theorem sourceWindow_phase_gap_far {N R : ℝ} (hN : 0 < N) (j : ℕ) (ξ : ℝ)
    (hv : -2 * Real.pi * ξ * Real.sqrt N = 1 / Real.sqrt R)
    (hRn : 4 * ((j : ℝ) + 2) < R) (w : ℝ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    sourceWindowScale N j * (((j : ℝ) + 2) / 6) ≤
      |sourceOscillatoryPhaseDeriv N j ξ w| := by
  have hn : (2 : ℝ) ≤ (j : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have ht : (j : ℝ) + w ∈ Icc (((j : ℝ) + 2) - 3 / 2) (((j : ℝ) + 2) + 3 / 2) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  rw [abs_sourceOscillatoryPhaseDeriv_normalized hN j hw, hv]
  exact mul_le_mul_of_nonneg_left (reciprocalSqrt_separation_far hn ht hRn)
    (sourceWindowScale_pos hN j).le

/-- Replacing a gap by an absolute constant multiple loses at most the square
of that constant in the smoothed inverse-square estimate. -/
theorem inverseSquare_scaled_gap_le {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) :
    1 / (1 + x / c) ^ 2 ≤ c ^ 2 / (1 + x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hlin : 1 + x ≤ c * (1 + x / c) := by
    have heq : c * (1 + x / c) = c + x := by
      field_simp
      <;> ring
    rw [heq]
    linarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul, mul_pow] using
    pow_le_pow_left₀ (show 0 ≤ 1 + x by positivity) hlin 2

end ProofProject
