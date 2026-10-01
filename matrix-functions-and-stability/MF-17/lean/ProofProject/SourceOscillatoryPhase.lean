import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The actual scalar phase of the source oscillatory windows

The linear frequency term uses Mathlib's `2π` normalization. Derivatives are
proved on the positive square-root domain, without a stationary-phase premise.
-/

noncomputable section

namespace ProofProject

/-- The rescaled positive phase, with the inverse Fourier frequency sign. -/
def sourceOscillatoryPhase (N : ℝ) (j : ℕ) (ξ w : ℝ) : ℝ :=
  2 * Real.sqrt (N * ((j : ℝ) + w)) + 2 * Real.pi * N * ξ * w

def sourceOscillatoryPhaseDeriv (N : ℝ) (j : ℕ) (ξ w : ℝ) : ℝ :=
  N / Real.sqrt (N * ((j : ℝ) + w)) + 2 * Real.pi * N * ξ

def sourceOscillatoryPhaseSecond (N : ℝ) (j : ℕ) (w : ℝ) : ℝ :=
  -(N ^ 2) / (2 * Real.sqrt (N * ((j : ℝ) + w)) ^ 3)

def sourceOscillatoryPhaseThird (N : ℝ) (j : ℕ) (w : ℝ) : ℝ :=
  3 * N ^ 3 / (4 * Real.sqrt (N * ((j : ℝ) + w)) ^ 5)

/-- The unique stationary frequency in Mathlib's Fourier coordinates. -/
def sourceStationaryFrequency (N : ℝ) (j : ℕ) (w : ℝ) : ℝ :=
  -1 / (2 * Real.pi * Real.sqrt (N * ((j : ℝ) + w)))

private theorem sourcePhaseRoot_hasDerivAt {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) :
    HasDerivAt (fun v : ℝ => Real.sqrt (N * ((j : ℝ) + v)))
      (N / (2 * Real.sqrt (N * ((j : ℝ) + w)))) w := by
  have hlin : HasDerivAt (fun v : ℝ => N * ((j : ℝ) + v)) N w := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id w).const_add (j : ℝ)).const_mul N
  exact hlin.sqrt (mul_pos hN hw).ne'

theorem sourceOscillatoryPhase_hasDerivAt {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    HasDerivAt (sourceOscillatoryPhase N j ξ) (sourceOscillatoryPhaseDeriv N j ξ w) w := by
  have hs : Real.sqrt (N * ((j : ℝ) + w)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hN hw)).ne'
  unfold sourceOscillatoryPhase
  refine (((sourcePhaseRoot_hasDerivAt hN hw).const_mul 2).add
    ((hasDerivAt_id w).const_mul (2 * Real.pi * N * ξ))).congr_deriv ?_
  unfold sourceOscillatoryPhaseDeriv
  field_simp [hs]

theorem sourceOscillatoryPhaseDeriv_hasDerivAt {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    HasDerivAt (sourceOscillatoryPhaseDeriv N j ξ)
      (sourceOscillatoryPhaseSecond N j w) w := by
  have hs : Real.sqrt (N * ((j : ℝ) + w)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hN hw)).ne'
  unfold sourceOscillatoryPhaseDeriv
  refine (((hasDerivAt_const w N).div (sourcePhaseRoot_hasDerivAt hN hw) hs).add_const
    (2 * Real.pi * N * ξ)).congr_deriv ?_
  unfold sourceOscillatoryPhaseSecond
  field_simp [hs] <;> ring

theorem sourceOscillatoryPhaseSecond_hasDerivAt {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) :
    HasDerivAt (sourceOscillatoryPhaseSecond N j)
      (sourceOscillatoryPhaseThird N j w) w := by
  have hs : Real.sqrt (N * ((j : ℝ) + w)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hN hw)).ne'
  have hden := ((sourcePhaseRoot_hasDerivAt hN hw).pow 3).const_mul 2
  unfold sourceOscillatoryPhaseSecond
  refine ((hasDerivAt_const w (-(N ^ 2))).div hden
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs))).congr_deriv ?_
  unfold sourceOscillatoryPhaseThird
  norm_num <;> field_simp [hs] <;> ring

theorem sourceOscillatoryPhase_deriv {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    deriv (sourceOscillatoryPhase N j ξ) w = sourceOscillatoryPhaseDeriv N j ξ w :=
  (sourceOscillatoryPhase_hasDerivAt hN hw ξ).deriv

theorem sourceOscillatoryPhase_second {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    deriv (sourceOscillatoryPhaseDeriv N j ξ) w = sourceOscillatoryPhaseSecond N j w :=
  (sourceOscillatoryPhaseDeriv_hasDerivAt hN hw ξ).deriv

theorem sourceOscillatoryPhase_third {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) :
    deriv (sourceOscillatoryPhaseSecond N j) w = sourceOscillatoryPhaseThird N j w :=
  (sourceOscillatoryPhaseSecond_hasDerivAt hN hw).deriv

/-- The second derivative has a fixed negative sign on the positive domain. -/
theorem sourceOscillatoryPhaseSecond_neg {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) :
    sourceOscillatoryPhaseSecond N j w < 0 := by
  unfold sourceOscillatoryPhaseSecond
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + w)) := Real.sqrt_pos.mpr (mul_pos hN hw)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hN)) (by positivity)

theorem sourceOscillatoryPhaseThird_pos {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) :
    0 < sourceOscillatoryPhaseThird N j w := by
  unfold sourceOscillatoryPhaseThird
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + w)) := Real.sqrt_pos.mpr (mul_pos hN hw)
  positivity

/-- Exact distance from the stationary frequency before absolute values. -/
theorem sourceOscillatoryPhaseDeriv_eq_frequency_sub {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    sourceOscillatoryPhaseDeriv N j ξ w =
      (2 * Real.pi * N) * (ξ - sourceStationaryFrequency N j w) := by
  have hs : Real.sqrt (N * ((j : ℝ) + w)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hN hw)).ne'
  unfold sourceOscillatoryPhaseDeriv sourceStationaryFrequency
  field_simp [hs, Real.pi_ne_zero] <;> ring

theorem sourceOscillatoryPhaseDeriv_eq_zero_iff {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    sourceOscillatoryPhaseDeriv N j ξ w = 0 ↔
      ξ = -1 / (2 * Real.pi * Real.sqrt (N * ((j : ℝ) + w))) := by
  rw [sourceOscillatoryPhaseDeriv_eq_frequency_sub hN hw]
  have hfac : 2 * Real.pi * N ≠ 0 := by positivity
  simp only [mul_eq_zero, hfac, false_or, sub_eq_zero, sourceStationaryFrequency]

theorem abs_sourceOscillatoryPhaseDeriv {N w : ℝ} {j : ℕ}
    (hN : 0 < N) (hw : 0 < (j : ℝ) + w) (ξ : ℝ) :
    |sourceOscillatoryPhaseDeriv N j ξ w| =
      (2 * Real.pi * N) * |ξ - sourceStationaryFrequency N j w| := by
  rw [sourceOscillatoryPhaseDeriv_eq_frequency_sub hN hw, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi * N)]

end ProofProject
