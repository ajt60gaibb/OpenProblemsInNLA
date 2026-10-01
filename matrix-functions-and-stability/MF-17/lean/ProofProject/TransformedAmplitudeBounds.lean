import ProofProject.SignedTransformedAmplitude

/-!
# Weighted estimates for the signed transformed amplitudes

The half-power transforms preserve the source's derivative weights after the
support scales are inserted. The derivative transform uses one more derivative
of the original amplitude. All constants precede the amplitude and its scales.
-/

noncomputable section

open Set Filter Finset
open scoped ContDiff Topology

namespace ProofProject

private theorem signed_imaginary_norm {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖Complex.I * (σ : ℂ)‖ = 1 := by
  rcases hσ with rfl | rfl <;> simp

theorem powerAmplitudeDerivativeConstant_half_le {n : ℕ} (hn : n ≤ 2) :
    powerAmplitudeDerivativeConstant (1 / 2) n ≤ 9 / 4 := by
  interval_cases n <;>
    norm_num [powerAmplitudeDerivativeConstant, rpowDerivativeCoefficient,
      Finset.sum_range_succ, Finset.prod_range_succ]

theorem powerAmplitudeDerivativeConstant_neg_half_le {n : ℕ} (hn : n ≤ 2) :
    powerAmplitudeDerivativeConstant (-1 / 2) n ≤ 11 / 4 := by
  interval_cases n <;>
    norm_num [powerAmplitudeDerivativeConstant, rpowDerivativeCoefficient,
      Finset.sum_range_succ, Finset.prod_range_succ]

theorem norm_iteratedDeriv_signedPrimitiveAmplitude
    (a : ℝ → ℂ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (signedPrimitiveAmplitude σ a) u‖ =
      ‖iteratedDeriv n (powerAmplitude (1 / 2) a) u‖ := by
  change ‖iteratedDeriv n (fun v =>
    (-Complex.I * (σ : ℂ)) * powerAmplitude (1 / 2) a v) u‖ = _
  rw [iteratedDeriv_const_mul_field, norm_mul]
  have h : ‖-Complex.I * (σ : ℂ)‖ = 1 := by
    rw [neg_mul, norm_neg]
    exact signed_imaginary_norm hσ
  rw [h, one_mul]

/-- The primitive transform has the half-power weight with constant at most
`9/4` for every derivative order at most two. -/
theorem norm_iteratedDeriv_signedPrimitiveAmplitude_le
    {a : ℝ → ℂ} {A σ u : ℝ} {n : ℕ} (ha : ContDiff ℝ ∞ a)
    (hA0 : 0 ≤ A) (hσ : σ = 1 ∨ σ = -1) (hn : n ≤ 2) (hu : 0 < u)
    (hA : ∀ j ≤ n, ‖iteratedDeriv j a u‖ ≤ A * u ^ (-3 / 4 - (j : ℝ))) :
    ‖iteratedDeriv n (signedPrimitiveAmplitude σ a) u‖ ≤
      (9 / 4) * A * u ^ (-1 / 4 - (n : ℝ)) := by
  rw [norm_iteratedDeriv_signedPrimitiveAmplitude a hσ n u]
  have h := norm_iteratedDeriv_powerAmplitude_le (1 / 2) (-3 / 4) n ha hA0 hu hA
  have hc := powerAmplitudeDerivativeConstant_half_le hn
  convert! h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc hA0) (Real.rpow_nonneg hu.le _)) using 1
  norm_num

/-- The first derivative has the sharper local coefficient `3/2`, needed in
the later nonstationary separator estimate. -/
theorem norm_deriv_signedPrimitiveAmplitude_le
    {a : ℝ → ℂ} {A σ u : ℝ} (ha : ContDiff ℝ ∞ a)
    (hA0 : 0 ≤ A) (hσ : σ = 1 ∨ σ = -1) (hu : 0 < u)
    (h0 : ‖a u‖ ≤ A * u ^ (-3 / 4 : ℝ))
    (h1 : ‖deriv a u‖ ≤ A * u ^ (-7 / 4 : ℝ)) :
    ‖deriv (signedPrimitiveAmplitude σ a) u‖ ≤
      (3 / 2) * A * u ^ (-5 / 4 : ℝ) := by
  rw [← iteratedDeriv_one, norm_iteratedDeriv_signedPrimitiveAmplitude a hσ 1 u]
  have hA : ∀ j ≤ 1, ‖iteratedDeriv j a u‖ ≤ A * u ^ (-3 / 4 - (j : ℝ)) := by
    intro j hj
    interval_cases j
    · simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using h0
    · norm_num only [iteratedDeriv_one, Nat.cast_one] at ⊢
      convert h1 using 1
      norm_num
  have h := norm_iteratedDeriv_powerAmplitude_le (1 / 2) (-3 / 4) 1 ha hA0 hu hA
  norm_num [powerAmplitudeDerivativeConstant, rpowDerivativeCoefficient,
    Finset.sum_range_succ, Finset.prod_range_succ] at h
  simpa only [iteratedDeriv_one, neg_div] using h

/-- The derivative transform's two different powers are kept separate before
the lower support scale is used. -/
theorem norm_iteratedDeriv_signedDerivativeAmplitude_le
    {a : ℝ → ℂ} {A σ u : ℝ} {n : ℕ} (ha : ContDiff ℝ ∞ a)
    (hA0 : 0 ≤ A) (hσ : σ = 1 ∨ σ = -1) (hn : n ≤ 2) (hu : 0 < u)
    (hA : ∀ j ≤ n + 1, ‖iteratedDeriv j a u‖ ≤ A * u ^ (-3 / 4 - (j : ℝ))) :
    ‖iteratedDeriv n (signedDerivativeAmplitude σ a) u‖ ≤
      A * u ^ (-3 / 4 - (n : ℝ)) * (u ^ (-1 : ℝ) + (11 / 4) * u ^ (-1 / 2 : ℝ)) := by
  have heq := iteratedDeriv_signedDerivativeAmplitude σ ha n hu
  rw [heq]
  have hadd := norm_add_le (iteratedDeriv (n + 1) a u)
    ((Complex.I * (σ : ℂ)) * iteratedDeriv n (powerAmplitude (-1 / 2) a) u)
  rw [norm_mul, signed_imaginary_norm hσ, one_mul] at hadd
  have hpower := norm_iteratedDeriv_powerAmplitude_le (-1 / 2) (-3 / 4) n ha hA0 hu
    (fun j hj => hA j (by omega))
  have hc := powerAmplitudeDerivativeConstant_neg_half_le hn
  have hpower' := hpower.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc hA0) (Real.rpow_nonneg hu.le _))
  refine (hadd.trans (add_le_add (hA (n + 1) le_rfl) hpower')).trans_eq ?_
  have h1 : u ^ (-3 / 4 - ((n + 1 : ℕ) : ℝ)) =
      u ^ (-3 / 4 - (n : ℝ)) * u ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hu]
    congr 1
    push_cast
    ring
  have h2 : u ^ (-1 / 2 + -3 / 4 - (n : ℝ)) =
      u ^ (-3 / 4 - (n : ℝ)) * u ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  rw [h1, h2]
  ring

/-- The upper support endpoint restores the original weights for the primitive
transform. A single coefficient works through derivative order two. -/
theorem signedPrimitiveAmplitude_weighted_bound
    {a : ℝ → ℂ} {A σ R : ℝ} (ha : ContDiff ℝ ∞ a)
    (hA0 : 0 ≤ A) (hσ : σ = 1 ∨ σ = -1) (_hR : 0 ≤ R)
    (hupper : ∀ u, 4 * R < u → a u = 0)
    (hA : ∀ n ≤ 2, ∀ u > 0,
      ‖iteratedDeriv n a u‖ ≤ A * u ^ (-3 / 4 - (n : ℝ))) :
    ∀ n ≤ 2, ∀ u > 0, ‖iteratedDeriv n (signedPrimitiveAmplitude σ a) u‖ ≤
      ((9 / 2) * A * Real.sqrt R) * u ^ (-3 / 4 - (n : ℝ)) := by
  intro n hn u hu
  by_cases hRu : u ≤ 4 * R
  · have hb := norm_iteratedDeriv_signedPrimitiveAmplitude_le ha hA0 hσ hn hu
      (fun j hj => hA j (hj.trans hn) u hu)
    have hsqrt : Real.sqrt u ≤ 2 * Real.sqrt R := by
      calc
        _ ≤ Real.sqrt (4 * R) := Real.sqrt_le_sqrt hRu
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
    have hpow : u ^ (-1 / 4 - (n : ℝ)) =
        Real.sqrt u * u ^ (-3 / 4 - (n : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hu]
      congr 1
      ring
    rw [hpow] at hb
    calc
      _ ≤ (9 / 4) * A * (Real.sqrt u * u ^ (-3 / 4 - (n : ℝ))) := hb
      _ ≤ (9 / 4) * A * ((2 * Real.sqrt R) * u ^ (-3 / 4 - (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hu.le _)) (by positivity)
      _ = _ := by ring
  · have hz : iteratedDeriv n (signedPrimitiveAmplitude σ a) u = 0 :=
      iteratedDeriv_eq_zero_of_upper_support (fun v hv => by
        simp [signedPrimitiveAmplitude, powerAmplitude, hupper v hv]) (lt_of_not_ge hRu) n
    rw [hz, norm_zero]
    positivity

/-- The lower support endpoint restores the original weights for the derivative
transform. The source condition `N ≥ 16` is stronger than the `N ≥ 1` used here. -/
theorem signedDerivativeAmplitude_weighted_bound
    {a : ℝ → ℂ} {A σ N : ℝ} (ha : ContDiff ℝ ∞ a)
    (hA0 : 0 ≤ A) (hσ : σ = 1 ∨ σ = -1) (hN : 1 ≤ N)
    (hlower : ∀ u < 2 * N, a u = 0)
    (hA : ∀ n ≤ 3, ∀ u > 0,
      ‖iteratedDeriv n a u‖ ≤ A * u ^ (-3 / 4 - (n : ℝ))) :
    ∀ n ≤ 2, ∀ u > 0, ‖iteratedDeriv n (signedDerivativeAmplitude σ a) u‖ ≤
      (4 * A / Real.sqrt N) * u ^ (-3 / 4 - (n : ℝ)) := by
  intro n hn u hu
  by_cases hNu : 2 * N ≤ u
  · have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
    have hNu' : N ≤ u := by linarith
    have hu1 : 1 ≤ u := hN.trans hNu'
    have hb := norm_iteratedDeriv_signedDerivativeAmplitude_le ha hA0 hσ hn hu
      (fun j hj => hA j (by omega) u hu)
    have hpow1 : u ^ (-1 : ℝ) ≤ u ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    have hpow2 : u ^ (-1 / 2 : ℝ) ≤ (Real.sqrt N)⁻¹ := by
      calc
        _ ≤ N ^ (-1 / 2 : ℝ) := Real.rpow_le_rpow_of_nonpos hN0 hNu' (by norm_num)
        _ = _ := by rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hN0.le,
          ← Real.sqrt_eq_rpow]
    have hsum : u ^ (-1 : ℝ) + (11 / 4) * u ^ (-1 / 2 : ℝ) ≤
        4 * (Real.sqrt N)⁻¹ := by
      have h0 := Real.rpow_nonneg hu.le (-1 / 2 : ℝ)
      nlinarith
    calc
      _ ≤ A * u ^ (-3 / 4 - (n : ℝ)) *
          (u ^ (-1 : ℝ) + (11 / 4) * u ^ (-1 / 2 : ℝ)) := hb
      _ ≤ A * u ^ (-3 / 4 - (n : ℝ)) * (4 * (Real.sqrt N)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  · have hzero : ∀ v < 2 * N, signedDerivativeAmplitude σ a v = 0 := by
      intro v hv
      have hd : deriv a v = 0 := by
        simpa only [iteratedDeriv_one] using iteratedDeriv_eq_zero_of_lower_support hlower hv 1
      simp [signedDerivativeAmplitude, powerAmplitude, hlower v hv, hd]
    rw [iteratedDeriv_eq_zero_of_lower_support hzero (lt_of_not_ge hNu) n, norm_zero]
    positivity

end ProofProject
