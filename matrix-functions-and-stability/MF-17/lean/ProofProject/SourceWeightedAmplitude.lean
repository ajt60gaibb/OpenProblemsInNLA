import ProofProject.SourceWindowAmplitude
import ProofProject.SourceWindowPhaseBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# From the original weighted amplitude bounds to scaled window bounds

The original powers through derivative order two give uniform estimates for
the actual scaled amplitude. All constants are independent of the scale and
window index, and the case of a zero amplitude bound is retained.
-/

noncomputable section

open Set
open scoped ContDiff

namespace ProofProject

/-- The center scale is exactly the square of the rescaled amplitude weight. -/
theorem sqrt_sourceWindowScale_eq {N : ℝ} (hN : 0 < N) (j : ℕ) :
    Real.sqrt (sourceWindowScale N j) =
      N * (N * ((j : ℝ) + 2)) ^ (-3 / 4 : ℝ) := by
  have hV : 0 < N * ((j : ℝ) + 2) := mul_pos hN (by positivity)
  have hden : Real.sqrt (Real.sqrt (N * ((j : ℝ) + 2)) ^ 3) =
      (N * ((j : ℝ) + 2)) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hV.le, ← Real.rpow_mul hV.le]
    norm_num
  rw [sourceWindowScale, Real.sqrt_div (sq_nonneg N), Real.sqrt_sq hN.le, hden,
    show (-3 / 4 : ℝ) = -(3 / 4 : ℝ) by ring, Real.rpow_neg hV.le]
  rfl

private theorem sourceWindow_weight_compare {U V : ℝ} (hV : 0 < V)
    (hVU : V / 4 ≤ U) : U ^ (-3 / 4 : ℝ) ≤ 4 * V ^ (-3 / 4 : ℝ) := by
  have hfour : (4 : ℝ) ^ (3 / 4 : ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (3 / 4 : ℝ) ≤ 1))
  have hneg : (4 : ℝ) ^ (-3 / 4 : ℝ) = ((4 : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [show (-3 / 4 : ℝ) = -(3 / 4 : ℝ) by ring, Real.rpow_neg (by norm_num)]
  calc
    _ ≤ (V / 4) ^ (-3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hVU (by norm_num)
    _ = V ^ (-3 / 4 : ℝ) * (4 : ℝ) ^ (3 / 4 : ℝ) := by
      rw [Real.div_rpow hV.le (by norm_num), hneg, div_inv_eq_mul]
    _ ≤ V ^ (-3 / 4 : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hfour (Real.rpow_nonneg hV.le _)
    _ = _ := mul_comm _ _

/-- The three chain-rule-scaled original weights have absolute bounds `4`,
`8`, and `16` relative to the center scale, including the first window. -/
theorem sourceWindow_scaled_weight_bounds {N w : ℝ} (hN : 0 < N) (j : ℕ)
    (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    N * (N * ((j : ℝ) + w)) ^ (-3 / 4 : ℝ) ≤
        4 * Real.sqrt (sourceWindowScale N j) ∧
      N ^ 2 * (N * ((j : ℝ) + w)) ^ (-3 / 4 - 1 : ℝ) ≤
        8 * Real.sqrt (sourceWindowScale N j) ∧
      N ^ 3 * (N * ((j : ℝ) + w)) ^ (-3 / 4 - 2 : ℝ) ≤
        16 * Real.sqrt (sourceWindowScale N j) := by
  let U := N * ((j : ℝ) + w)
  let V := N * ((j : ℝ) + 2)
  have hU : 0 < U := mul_pos hN (by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1])
  have hV : 0 < V := mul_pos hN (by positivity)
  have hbase : N * U ^ (-3 / 4 : ℝ) ≤ 4 * Real.sqrt (sourceWindowScale N j) := by
    rw [sqrt_sourceWindowScale_eq hN j]
    have h := mul_le_mul_of_nonneg_left
      (sourceWindow_weight_compare hV (sourceWindow_argument_bounds hN j hw).1) hN.le
    dsimp only [U, V] at h
    nlinarith
  have hratio : N / U ≤ 2 := by
    apply (div_le_iff₀ hU).mpr
    have h := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 2 * ((j : ℝ) + w) by
        have := Nat.cast_nonneg (α := ℝ) j
        linarith [hw.1]) hN.le
    dsimp only [U]
    nlinarith
  have hratio0 : 0 ≤ N / U := div_nonneg hN.le hU.le
  refine ⟨hbase, ?_, ?_⟩
  · change N ^ 2 * U ^ (-3 / 4 - 1 : ℝ) ≤ _
    calc
      _ = (N * U ^ (-3 / 4 : ℝ)) * (N / U) := by
        rw [Real.rpow_sub hU, Real.rpow_one]
        ring
      _ ≤ (4 * Real.sqrt (sourceWindowScale N j)) * 2 :=
        mul_le_mul hbase hratio hratio0 (by positivity)
      _ = _ := by ring
  · change N ^ 3 * U ^ (-3 / 4 - 2 : ℝ) ≤ _
    calc
      _ = (N * U ^ (-3 / 4 : ℝ)) * (N / U) ^ 2 := by
        rw [Real.rpow_sub hU, Real.rpow_two]
        ring
      _ ≤ (4 * Real.sqrt (sourceWindowScale N j)) * 2 ^ 2 :=
        mul_le_mul hbase (pow_le_pow_left₀ hratio0 hratio 2) (sq_nonneg _) (by positivity)
      _ = _ := by ring

/-- The original three weighted bounds control the three terms before the
cutoff product rule. No division by the amplitude constant is used. -/
theorem sourceWindow_scaled_amplitude_terms {A0 N w : ℝ} (hA0 : 0 ≤ A0) (hN : 0 < N)
    {a : ℝ → ℂ}
    (h0 : ∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ))
    (h1 : ∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ))
    (h2 : ∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ))
    (j : ℕ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    N * ‖a (N * ((j : ℝ) + w))‖ ≤ 4 * A0 * Real.sqrt (sourceWindowScale N j) ∧
      N ^ 2 * ‖deriv a (N * ((j : ℝ) + w))‖ ≤ 8 * A0 * Real.sqrt (sourceWindowScale N j) ∧
      N ^ 3 * ‖deriv (deriv a) (N * ((j : ℝ) + w))‖ ≤
        16 * A0 * Real.sqrt (sourceWindowScale N j) := by
  have hU : 0 < N * ((j : ℝ) + w) := mul_pos hN (by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1])
  obtain ⟨hb0, hb1, hb2⟩ := sourceWindow_scaled_weight_bounds hN j hw
  have transfer {t B W K : ℝ} (ht : 0 ≤ t) (hB : B ≤ A0 * W)
      (hW : t * W ≤ K * Real.sqrt (sourceWindowScale N j)) :
      t * B ≤ K * A0 * Real.sqrt (sourceWindowScale N j) := by
    calc
      _ ≤ t * (A0 * W) := mul_le_mul_of_nonneg_left hB ht
      _ = A0 * (t * W) := by ring
      _ ≤ A0 * (K * Real.sqrt (sourceWindowScale N j)) :=
        mul_le_mul_of_nonneg_left hW hA0
      _ = _ := by ring
  exact ⟨transfer hN.le (h0 _ hU) hb0,
    transfer (sq_nonneg N) (h1 _ hU) hb1,
    transfer (pow_nonneg hN.le 3) (h2 _ hU) hb2⟩

/-- Original weighted derivative estimates imply the actual scaled bounds
with constants `4D`, `12D`, and `36D` for a single fixed cutoff constant. -/
theorem sourceWindowAmplitude_bounds_of_weighted {A0 D N w : ℝ}
    (hA0 : 0 ≤ A0) (hD : 1 ≤ D) (hN : 0 < N) {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a)
    (hD1 : ∀ v : ℝ, ‖deriv sourceTriangleCutoff v‖ ≤ D)
    (hD2 : ∀ v : ℝ, ‖deriv (deriv sourceTriangleCutoff) v‖ ≤ D)
    (h0 : ∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ))
    (h1 : ∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ))
    (h2 : ∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ))
    (j : ℕ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    ‖sourceWindowAmplitude N a j w‖ ≤ 4 * D * A0 * Real.sqrt (sourceWindowScale N j) ∧
      ‖deriv (sourceWindowAmplitude N a j) w‖ ≤
        12 * D * A0 * Real.sqrt (sourceWindowScale N j) ∧
      ‖deriv (deriv (sourceWindowAmplitude N a j)) w‖ ≤
        36 * D * A0 * Real.sqrt (sourceWindowScale N j) := by
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  have hDS : A0 * Real.sqrt (sourceWindowScale N j) ≤
      D * (A0 * Real.sqrt (sourceWindowScale N j)) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hD (mul_nonneg hA0 (Real.sqrt_nonneg _))
  obtain ⟨hb0, hb1, hb2⟩ := sourceWindow_scaled_amplitude_terms hA0 hN h0 h1 h2 j hw
  refine ⟨?_, ?_, ?_⟩
  · exact (sourceWindowAmplitude_norm_le hN.le a j w).trans
      (hb0.trans (by nlinarith [hDS]))
  · rw [deriv_sourceWindowAmplitude N (contDiff_infty_iff_deriv.mp ha).1 j]
    calc
      _ ≤ N ^ 2 * ‖deriv a (N * ((j : ℝ) + w))‖ +
          (N * ‖a (N * ((j : ℝ) + w))‖) * D :=
        norm_sourceWindowAmplitudeFirst_le hN.le a (deriv a) j w (hD1 w)
      _ ≤ 8 * A0 * Real.sqrt (sourceWindowScale N j) +
          (4 * A0 * Real.sqrt (sourceWindowScale N j)) * D :=
        add_le_add hb1 (mul_le_mul_of_nonneg_right hb0 hD0)
      _ ≤ _ := by nlinarith [hDS]
  · rw [deriv_twice_sourceWindowAmplitude N ha j]
    calc
      _ ≤ N ^ 3 * ‖deriv (deriv a) (N * ((j : ℝ) + w))‖ +
          2 * (N ^ 2 * ‖deriv a (N * ((j : ℝ) + w))‖) * D +
            (N * ‖a (N * ((j : ℝ) + w))‖) * D := by
        simpa only [mul_assoc] using norm_sourceWindowAmplitudeSecond_le hN.le
          a (deriv a) (deriv (deriv a)) j w (hD1 w) (hD2 w)
      _ ≤ 16 * A0 * Real.sqrt (sourceWindowScale N j) +
          2 * (8 * A0 * Real.sqrt (sourceWindowScale N j)) * D +
            (4 * A0 * Real.sqrt (sourceWindowScale N j)) * D :=
        add_le_add (add_le_add hb2
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hD0))
          (mul_le_mul_of_nonneg_right hb0 hD0)
      _ ≤ _ := by nlinarith [hDS]

/-- One common constant supplies all scaled-amplitude hypotheses of the
already proved stationary and nonstationary window estimates. -/
theorem sourceWindowAmplitude_bounds_of_weighted_common {A0 D N w : ℝ}
    (hA0 : 0 ≤ A0) (hD : 1 ≤ D) (hN : 0 < N) {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a)
    (hD1 : ∀ v : ℝ, ‖deriv sourceTriangleCutoff v‖ ≤ D)
    (hD2 : ∀ v : ℝ, ‖deriv (deriv sourceTriangleCutoff) v‖ ≤ D)
    (h0 : ∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ))
    (h1 : ∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ))
    (h2 : ∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ))
    (j : ℕ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    ‖sourceWindowAmplitude N a j w‖ ≤ 40 * D * A0 * Real.sqrt (sourceWindowScale N j) ∧
      ‖deriv (sourceWindowAmplitude N a j) w‖ ≤
        40 * D * A0 * Real.sqrt (sourceWindowScale N j) ∧
      ‖deriv (deriv (sourceWindowAmplitude N a j)) w‖ ≤
        40 * D * A0 * Real.sqrt (sourceWindowScale N j) := by
  obtain ⟨hb0, hb1, hb2⟩ :=
    sourceWindowAmplitude_bounds_of_weighted hA0 hD hN ha hD1 hD2 h0 h1 h2 j hw
  have hnonneg : 0 ≤ D * A0 * Real.sqrt (sourceWindowScale N j) :=
    mul_nonneg (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans hD) hA0) (Real.sqrt_nonneg _)
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The common cutoff constant is chosen before the amplitude, scale, window,
and evaluation point. Thus the weighted-to-scaled bounds are fully uniform. -/
theorem exists_sourceWindowAmplitude_weighted_bound :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (A0 : ℝ), 0 ≤ A0 → ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) →
      (∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) →
      (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) →
      ∀ (N : ℝ), 0 < N → ∀ (j : ℕ) (w : ℝ), w ∈ Icc (1 / 2 : ℝ) (7 / 2) →
        ‖sourceWindowAmplitude N a j w‖ ≤ 40 * D * A0 * Real.sqrt (sourceWindowScale N j) ∧
          ‖deriv (sourceWindowAmplitude N a j) w‖ ≤
            40 * D * A0 * Real.sqrt (sourceWindowScale N j) ∧
          ‖deriv (deriv (sourceWindowAmplitude N a j)) w‖ ≤
            40 * D * A0 * Real.sqrt (sourceWindowScale N j) := by
  obtain ⟨D, hD, hDb⟩ := exists_sourceTriangleCutoff_derivative_bound
  refine ⟨D, hD, ?_⟩
  intro A0 hA0 a ha h0 h1 h2 N hN j w hw
  exact sourceWindowAmplitude_bounds_of_weighted_common hA0 hD hN ha
    (fun v => (hDb v).2.1) (fun v => (hDb v).2.2) h0 h1 h2 j hw

end ProofProject
