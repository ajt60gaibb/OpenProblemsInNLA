import NLA.FR05.SmallBall.SourceNonTailGlobal
import NLA.FR05.Planted.SourceJacobianMatrix

/-!
# Source row small-ball bounds and calibration

The sections develop `SourceRowSmallBall`, `SmallBallCalibration`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section SourceRowSmallBall

/-
Combine the two source-faithful conditional branches of Lemma 3.6.

For every unit source-Jacobian direction, its energy is either tail-dominated
or scalar-dominated. The preceding global branch estimates therefore yield a
single explicit row small-ball bound under the exact manuscript source law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The tail-dominated bound at the manuscript radial cutoff. -/
def sourceTailSmallBallBound (M : ℕ) (u t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (4 * t) +
    ENNReal.ofReal
      (2 * u * Real.sqrt (8 * (M : ℝ)) /
        (Real.sqrt (2 * Real.pi) * t))) +
    (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ))))

/-- The scalar-dominated source row bound. -/
def sourceNonTailSmallBallBound (u t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
    ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t))

/-- Exact source-law row small-ball estimate for a unit source-Jacobian
direction. This is the two-branch content of Lemma 3.6 before selecting a
common numerical scale for `t` and before the row-to-span argument. -/
theorem sourceCoordinateLaw_sourceM_sourceJacobianRowSmallBall_le_max
    {M n : ℕ} (hM : 1 ≤ M) (x : SourceJacobianVector n) (hunit : sourceJacobianEnergy x = 1)
    (u t : ℝ) (hu : 0 ≤ u) (ht : 0 < t) (hscale : 2 * u ≤ t) :
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        (sourceRowJacobianSmallBallEvent
          (sourceJacobianP x) (sourceJacobianQ x) (x .sigma) (x .beta) (x .gamma) u) ≤
      max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) := by
  rcases sourceJacobian_scalar_or_tail_tailEnergy_ge_quarter x hunit with htail | hscalar
  · calc
      sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
          (sourceRowJacobianSmallBallEvent
            (sourceJacobianP x) (sourceJacobianQ x) (x .sigma) (x .beta) (x .gamma) u) ≤
          sourceTailSmallBallBound M u t := by
            simpa only [sourceTailSmallBallBound] using
              (sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_le
                hM (sourceJacobianP x) (sourceJacobianQ x)
                (x .sigma) (x .beta) (x .gamma) u t hu ht htail)
      _ ≤ max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) :=
        le_max_left _ _
  · calc
      sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
          (sourceRowJacobianSmallBallEvent
            (sourceJacobianP x) (sourceJacobianQ x) (x .sigma) (x .beta) (x .gamma) u) ≤
          sourceNonTailSmallBallBound u t := by
            simpa only [sourceNonTailSmallBallBound] using
              (sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_nonTail_le
                hM (sourceJacobianP x) (sourceJacobianQ x)
                (x .sigma) (x .beta) (x .gamma) u t ht hscale hscalar)
      _ ≤ max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) :=
        le_max_right _ _

end SourceRowSmallBall

section SmallBallCalibration

open scoped ENNReal

theorem source_smallBall_calibration {m u : ℝ} (hm : 2 ≤ m)
    (_hu : 0 ≤ u) (hub : u ≤ 4 / m ^ 11) :
    2 * u ≤ 1 / m ^ 6 ∧
    4 * (1 / m ^ 6) + 2 * u * Real.sqrt (8 * m) /
        (Real.sqrt (2 * Real.pi) * (1 / m ^ 6)) ≤ 28 / m ^ 3 ∧
    2 * Real.sqrt (2 * (1 / m ^ 6)) +
      6 * u / (Real.sqrt (2 * Real.pi) * (1 / m ^ 6)) ≤ 28 / m ^ 3 := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hmne : m ≠ 0 := ne_of_gt hm0
  have hp : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.two_le_pi]
  have hs : Real.sqrt (8 * m) ≤ 3 * m := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  have ht : Real.sqrt (2 * (1 / m ^ 6)) ≤ 2 / m ^ 3 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · field_simp
      nlinarith [sq_nonneg (m ^ 3)]
  have hpow : 8 ≤ m ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 5
    norm_num at h
    linarith
  have hscale : 8 / m ^ 11 ≤ 1 / m ^ 6 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      8 * m ^ 6 ≤ m ^ 5 * m ^ 6 := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 * m ^ 11 := by ring
  have hb1 : 2 * u * Real.sqrt (8 * m) /
      (Real.sqrt (2 * Real.pi) * (1 / m ^ 6)) ≤ 24 / m ^ 4 := by
    calc
      _ ≤ (2 * (4 / m ^ 11) * (3 * m)) / (1 * (1 / m ^ 6)) := by
        gcongr
      _ = 24 / m ^ 4 := by field_simp; ring
  have hb2 : 6 * u / (Real.sqrt (2 * Real.pi) * (1 / m ^ 6)) ≤ 24 / m ^ 5 := by
    calc
      _ ≤ (6 * (4 / m ^ 11)) / (1 * (1 / m ^ 6)) := by gcongr
      _ = 24 / m ^ 5 := by field_simp; ring
  have h34 : m ^ 3 ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by lia)
  have h35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by lia)
  have h36 : m ^ 3 ≤ m ^ 6 := pow_le_pow_right₀ hm1 (by lia)
  refine ⟨(show 2 * u ≤ 8 / m ^ 11 by have h := mul_le_mul_of_nonneg_left hub (by norm_num : (0 : ℝ) ≤ 2); simpa only [div_eq_mul_inv, ← mul_assoc, show (2 : ℝ) * 4 = 8 by norm_num] using h).trans hscale, ?_, ?_⟩
  · have h1 : 4 * (1 / m ^ 6) ≤ 4 / m ^ 3 := by
      simpa only [div_eq_mul_inv, one_mul] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
        (by positivity : 0 < m ^ 3) h36
    have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 24)
      (by positivity : 0 < m ^ 3) h34
    simp only [div_eq_mul_inv] at *
    linarith
  · have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 24)
      (by positivity : 0 < m ^ 3) h35
    simp only [div_eq_mul_inv] at *
    linarith

theorem source_row_threshold_le {M : ℕ} (hM : 2 ≤ M) :
    (sourceRowCount M : ℝ) * sourceKappa M ≤ 4 / (M : ℝ) ^ 11 := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by lia)
  have hn : (sourceRowCount M : ℝ) ≤ 4 * M := by
    exact_mod_cast (show sourceRowCount M ≤ 4 * M by unfold sourceRowCount; lia)
  unfold sourceKappa
  calc
    _ ≤ (4 * M) / (M : ℝ) ^ 12 := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ ((M : ℝ) ^ 12)⁻¹)
    _ = 4 / (M : ℝ) ^ 11 := by field_simp

theorem source_smallBall_bound_calibrated {M : ℕ} (hM : 2 ≤ M) :
    max (sourceTailSmallBallBound M
        ((sourceRowCount M : ℝ) * sourceKappa M) (1 / (M : ℝ) ^ 6))
      (sourceNonTailSmallBallBound
        ((sourceRowCount M : ℝ) * sourceKappa M) (1 / (M : ℝ) ^ 6)) ≤
      ENNReal.ofReal (28 / (M : ℝ) ^ 3 + 25 * Real.exp (-(4 * (M : ℝ)))) := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by lia)
  have hu : 0 ≤ (sourceRowCount M : ℝ) * sourceKappa M :=
    mul_nonneg (Nat.cast_nonneg _) (sourceKappa_pos M (by lia)).le
  obtain ⟨_, ht, hn⟩ := source_smallBall_calibration (by exact_mod_cast hM) hu
    (source_row_threshold_le hM)
  apply max_le
  · unfold sourceTailSmallBallBound
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      show (25 : ℝ≥0∞) = ENNReal.ofReal (25 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · unfold sourceNonTailSmallBallBound
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hn.trans (le_add_of_nonneg_right (by positivity)))

end SmallBallCalibration

end NLA.FR05
