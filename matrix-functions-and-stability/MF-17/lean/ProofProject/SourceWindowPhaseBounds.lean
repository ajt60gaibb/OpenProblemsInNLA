import ProofProject.SourceWindowStationary

/-!
# A single scale for the source-window phase derivatives

On the fixed cutoff interval, the center scale controls both curvature and
the first two derivatives of the phase derivative. The frequency-gap lemma
retains Mathlib's exact `2π` normalization.
-/

noncomputable section

namespace ProofProject

open Set

/-- The center curvature scale of a rescaled source window. -/
def sourceWindowScale (N : ℝ) (j : ℕ) : ℝ :=
  N ^ 2 / Real.sqrt (N * ((j : ℝ) + 2)) ^ 3

theorem sourceWindowScale_pos {N : ℝ} (hN : 0 < N) (j : ℕ) :
    0 < sourceWindowScale N j := by
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + 2)) :=
    Real.sqrt_pos.mpr (mul_pos hN (by positivity))
  unfold sourceWindowScale
  positivity

/-- All square-root arguments on the source window are comparable to the
argument at its center, including the first window and both endpoints. -/
theorem sourceWindow_argument_bounds {N w : ℝ} (hN : 0 < N) (j : ℕ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    N * ((j : ℝ) + 2) / 4 ≤ N * ((j : ℝ) + w) ∧
      N * ((j : ℝ) + w) ≤ 2 * (N * ((j : ℝ) + 2)) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlo := mul_le_mul_of_nonneg_left (show (j : ℝ) + 2 ≤ 4 * ((j : ℝ) + w) by
    linarith [hw.1]) hN.le
  have hhi := mul_le_mul_of_nonneg_left (show (j : ℝ) + w ≤ 2 * ((j : ℝ) + 2) by
    linarith [hw.2]) hN.le
  constructor <;> nlinarith

theorem sourceWindow_sqrt_bounds {N w : ℝ} (hN : 0 < N) (j : ℕ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    Real.sqrt (N * ((j : ℝ) + 2)) / 2 ≤ Real.sqrt (N * ((j : ℝ) + w)) ∧
      Real.sqrt (N * ((j : ℝ) + w)) ≤ 2 * Real.sqrt (N * ((j : ℝ) + 2)) := by
  have hjw : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  have hU : 0 < N * ((j : ℝ) + w) := mul_pos hN hjw
  have hV : 0 < N * ((j : ℝ) + 2) := mul_pos hN (by positivity)
  obtain ⟨hlo, hhi⟩ := sourceWindow_argument_bounds hN j hw
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hU.le]
  · apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hV.le]

/-- The lower curvature used by the second-derivative estimate loses at most
the absolute factor `16` from the center scale. -/
theorem sourceWindowScale_le_curvature {N : ℝ} (hN : 0 < N) (j : ℕ) :
    sourceWindowScale N j / 16 ≤ sourceWindowCurvature N j := by
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + 2)) :=
    Real.sqrt_pos.mpr (mul_pos hN (by positivity))
  have ht : 0 < Real.sqrt (N * ((j : ℝ) + 7 / 2)) :=
    Real.sqrt_pos.mpr (mul_pos hN (by positivity))
  have hbound := (sourceWindow_sqrt_bounds hN j (w := 7 / 2)
    ⟨by norm_num, le_rfl⟩).2
  unfold sourceWindowScale sourceWindowCurvature
  calc
    N ^ 2 / Real.sqrt (N * ((j : ℝ) + 2)) ^ 3 / 16 =
        N ^ 2 / (2 * (2 * Real.sqrt (N * ((j : ℝ) + 2))) ^ 3) := by
      field_simp
      <;> ring
    _ ≤ N ^ 2 / (2 * Real.sqrt (N * ((j : ℝ) + 7 / 2)) ^ 3) := by
      apply div_le_div_of_nonneg_left (sq_nonneg N) (by positivity)
      gcongr

theorem abs_sourceWindowPhaseSecond_le {N w : ℝ} (hN : 0 < N) (j : ℕ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    |sourceOscillatoryPhaseSecond N j w| ≤ 4 * sourceWindowScale N j := by
  have hjw : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + 2)) :=
    Real.sqrt_pos.mpr (mul_pos hN (by positivity))
  have ht : 0 < Real.sqrt (N * ((j : ℝ) + w)) :=
    Real.sqrt_pos.mpr (mul_pos hN hjw)
  have hbound := (sourceWindow_sqrt_bounds hN j hw).1
  rw [abs_of_neg (sourceOscillatoryPhaseSecond_neg hN hjw)]
  unfold sourceOscillatoryPhaseSecond sourceWindowScale
  rw [neg_div, neg_neg]
  calc
    N ^ 2 / (2 * Real.sqrt (N * ((j : ℝ) + w)) ^ 3) ≤
        N ^ 2 / (2 * (Real.sqrt (N * ((j : ℝ) + 2)) / 2) ^ 3) := by
      apply div_le_div_of_nonneg_left (sq_nonneg N) (by positivity)
      gcongr
    _ = 4 * (N ^ 2 / Real.sqrt (N * ((j : ℝ) + 2)) ^ 3) := by
      field_simp
      <;> ring

theorem abs_sourceWindowPhaseThird_le {N w : ℝ} (hN : 0 < N) (j : ℕ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    |sourceOscillatoryPhaseThird N j w| ≤ 24 * sourceWindowScale N j := by
  have hjw : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  have hV : 0 < N * ((j : ℝ) + 2) := mul_pos hN (by positivity)
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + 2)) := Real.sqrt_pos.mpr hV
  have ht : 0 < Real.sqrt (N * ((j : ℝ) + w)) :=
    Real.sqrt_pos.mpr (mul_pos hN hjw)
  have hNV : N ≤ N * ((j : ℝ) + 2) :=
    le_mul_of_one_le_right hN.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hnum : 3 * N ^ 3 ≤ 3 * N ^ 2 * (N * ((j : ℝ) + 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hNV (by positivity : 0 ≤ 3 * N ^ 2)]
  have hbound := (sourceWindow_sqrt_bounds hN j hw).1
  rw [abs_of_pos (sourceOscillatoryPhaseThird_pos hN hjw)]
  unfold sourceOscillatoryPhaseThird sourceWindowScale
  calc
    3 * N ^ 3 / (4 * Real.sqrt (N * ((j : ℝ) + w)) ^ 5) ≤
        3 * N ^ 2 * (N * ((j : ℝ) + 2)) /
          (4 * (Real.sqrt (N * ((j : ℝ) + 2)) / 2) ^ 5) := by
      apply div_le_div₀ (by positivity) hnum (by positivity)
      gcongr
    _ = 24 * (N ^ 2 / Real.sqrt (N * ((j : ℝ) + 2)) ^ 3) := by
      nth_rw 1 [← Real.sq_sqrt hV.le]
      field_simp [hs.ne']
      <;> ring

/-- A normalized distance from each stationary frequency gives precisely the
phase-derivative lower bound used in the nonstationary estimate. -/
theorem sourceWindow_frequency_gap {N w ξ s : ℝ} (hN : 0 < N) (j : ℕ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2))
    (hgap : N / (2 * Real.pi * Real.sqrt (N * ((j : ℝ) + 2)) ^ 3) * s ≤
      |ξ - sourceStationaryFrequency N j w|) :
    sourceWindowScale N j * s ≤ |sourceOscillatoryPhaseDeriv N j ξ w| := by
  have hjw : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  rw [abs_sourceOscillatoryPhaseDeriv hN hjw ξ]
  calc
    sourceWindowScale N j * s =
        (2 * Real.pi * N) *
          (N / (2 * Real.pi * Real.sqrt (N * ((j : ℝ) + 2)) ^ 3) * s) := by
      unfold sourceWindowScale
      field_simp [Real.pi_ne_zero]
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)

end ProofProject
