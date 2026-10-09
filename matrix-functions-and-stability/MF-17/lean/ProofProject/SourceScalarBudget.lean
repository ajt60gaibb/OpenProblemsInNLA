import ProofProject.SourceWindowSmoothedDecay
import ProofProject.SourceWindowPointwise
import ProofProject.FiniteLatticeDecay
import ProofProject.SourceAmplitudeConjugation

/-!
# The uniform finite scalar budget for the source windows

Original weighted derivative bounds imply a uniform sum over any finite set
of windows. Pointwise reciprocal-square-root separation supplies the derivative
gaps directly; finite lattice estimates control the resulting majorants.
-/

noncomputable section
open Set Finset
open scoped ContDiff
namespace ProofProject

private theorem sum_source_center_decay (J : Finset ℕ) :
    (∑ j ∈ J, 1 / (1 + ((j : ℝ) + 2)) ^ 2) ≤ 1 / 2 := by
  have h := sum_nat_inverse_square_le_half (J.image (fun j => j + 2)) (by
    intro n hn
    obtain ⟨j, _, rfl⟩ := mem_image.mp hn
    omega)
  rw [sum_image (by intro i _ j _ hij; dsimp at hij; omega)] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

private theorem sum_source_translated_decay (J : Finset ℕ) (R : ℝ) :
    (∑ j ∈ J, 1 / (1 + max 0 (|R - ((j : ℝ) + 2)| - 3 / 2)) ^ 2) ≤ 7 := by
  have h := sum_lattice_decay_le_seven (J.image (fun j => ((j + 2 : ℕ) : ℤ))) R
  rw [sum_image (by intro i _ j _ hij; exact Nat.add_right_cancel (Int.ofNat_inj.mp hij))] at h
  simpa only [Int.cast_natCast, Int.cast_add, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat] using h

/-- One absolute constant bounds the sum of the actual positive-phase Fourier
coefficients, uniformly over every finite set of windows and frequency. -/
theorem exists_sourceScalarBudget_positive :
    ∃ K : ℝ, 0 < K ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) →
      (∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) →
      (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) →
      ∀ N : ℝ, 0 < N →
      (∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0) →
      ∀ (J : Finset ℕ) (ξ : ℝ),
      (∑ j ∈ J, ‖triangularKernelCoefficient N (oscillatoryKernel 1 a)
        sourceTriangleCutoff j ξ‖) ≤ K * A0 := by
  obtain ⟨K, hK, hbudget⟩ := exists_sourceWindowCoefficient_smoothed_bound
  refine ⟨750 * K, by positivity, ?_⟩
  intro A0 hA0 a ha h0 h1 h2 N hN hsupp J ξ
  have hKA : 0 ≤ K * A0 := mul_nonneg hK.le hA0
  let v := -2 * Real.pi * ξ * Real.sqrt N
  let f : ℕ → ℝ := fun j => 1 / (1 + ((j : ℝ) + 2)) ^ 2
  have hf : ∑ j ∈ J, f j ≤ 1 / 2 := sum_source_center_decay J
  have hpoint (j : ℕ) (s : ℝ) (hs : 0 ≤ s)
      (hsep : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
        sourceWindowScale N j * s ≤ |sourceOscillatoryPhaseDeriv N j ξ w|) :=
    hbudget A0 hA0 a ha h0 h1 h2 N hN hsupp j ξ s hs hsep
  by_cases hv : v ≤ 0
  · have hb (j : ℕ) : ‖triangularKernelCoefficient N (oscillatoryKernel 1 a)
        sourceTriangleCutoff j ξ‖ ≤ 4 * K * A0 * f j := by
      have hraw := hpoint j (((j : ℝ) + 2) / 2) (by positivity)
        (fun w hw => sourceWindow_phase_gap_nonpos hN j ξ hv w hw)
      calc
        _ ≤ K * A0 / (1 + ((j : ℝ) + 2) / 2) ^ 2 := hraw
        _ = (K * A0) * (1 / (1 + ((j : ℝ) + 2) / 2) ^ 2) := by ring
        _ ≤ (K * A0) * (2 ^ 2 / (1 + ((j : ℝ) + 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left (inverseSquare_scaled_gap_le (by positivity) (by norm_num)) hKA
        _ = _ := by dsimp only [f]; ring
    calc
      _ ≤ ∑ j ∈ J, 4 * K * A0 * f j := sum_le_sum (fun j _ => hb j)
      _ = (4 * K * A0) * ∑ j ∈ J, f j := (mul_sum ..).symm
      _ ≤ (4 * K * A0) * (1 / 2) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ _ := by nlinarith
  · have hvp : 0 < v := lt_of_not_ge hv
    let R := 1 / v ^ 2
    have hR : 0 < R := by dsimp [R]; positivity
    have hvR : v = 1 / Real.sqrt R := (reciprocalSqrt_inv_sq hvp).symm
    let d : ℕ → ℝ := fun j => max 0 (|R - ((j : ℝ) + 2)| - 3 / 2)
    let g : ℕ → ℝ := fun j => 1 / (1 + d j) ^ 2
    have hg : ∑ j ∈ J, g j ≤ 7 := sum_source_translated_decay J R
    have hb (j : ℕ) : ‖triangularKernelCoefficient N (oscillatoryKernel 1 a)
        sourceTriangleCutoff j ξ‖ ≤ 100 * K * A0 * (f j + g j) := by
      have hn : 0 ≤ (j : ℝ) + 2 := by positivity
      have hd : 0 ≤ d j := le_max_left _ _
      have hf0 : 0 ≤ f j := by dsimp [f]; positivity
      have hg0 : 0 ≤ g j := by dsimp [g]; positivity
      by_cases hnear : R ≤ 4 * ((j : ℝ) + 2)
      · have hraw := hpoint j (d j / 10) (by positivity)
          (fun w hw => sourceWindow_phase_gap_near hN j ξ hR hvR hnear w hw)
        have hr := inverseSquare_scaled_gap_le hd (by norm_num : (1 : ℝ) ≤ 10)
        calc
          _ ≤ K * A0 / (1 + d j / 10) ^ 2 := hraw
          _ = (K * A0) * (1 / (1 + d j / 10) ^ 2) := by ring
          _ ≤ (K * A0) * (10 ^ 2 / (1 + d j) ^ 2) := mul_le_mul_of_nonneg_left hr hKA
          _ = 100 * K * A0 * g j := by dsimp [g]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      · have hfar : 4 * ((j : ℝ) + 2) < R := lt_of_not_ge hnear
        have hraw := hpoint j (((j : ℝ) + 2) / 6) (by positivity)
          (fun w hw => sourceWindow_phase_gap_far hN j ξ hvR hfar w hw)
        have hr := inverseSquare_scaled_gap_le hn (by norm_num : (1 : ℝ) ≤ 6)
        calc
          _ ≤ K * A0 / (1 + ((j : ℝ) + 2) / 6) ^ 2 := hraw
          _ = (K * A0) * (1 / (1 + ((j : ℝ) + 2) / 6) ^ 2) := by ring
          _ ≤ (K * A0) * (6 ^ 2 / (1 + ((j : ℝ) + 2)) ^ 2) := mul_le_mul_of_nonneg_left hr hKA
          _ = 36 * K * A0 * f j := by dsimp [f]; ring
          _ ≤ _ := by nlinarith [mul_nonneg hKA hf0, mul_nonneg hKA hg0]
    calc
      _ ≤ ∑ j ∈ J, 100 * K * A0 * (f j + g j) := sum_le_sum (fun j _ => hb j)
      _ = (100 * K * A0) * ((∑ j ∈ J, f j) + ∑ j ∈ J, g j) := by
        rw [← mul_sum, sum_add_distrib]
      _ ≤ (100 * K * A0) * (1 / 2 + 7) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring

/-- Both source signs share one scalar budget. The negative sign conjugates
the amplitude, preserving all real-derivative norms and the support bound. -/
theorem exists_sourceScalarBudget_signed :
    ∃ K : ℝ, 0 < K ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) →
      (∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) →
      (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) →
      ∀ N : ℝ, 0 < N →
      (∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0) →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ (J : Finset ℕ) (ξ : ℝ),
      (∑ j ∈ J, ‖triangularKernelCoefficient N (oscillatoryKernel σ a)
        sourceTriangleCutoff j ξ‖) ≤ K * A0 := by
  obtain ⟨K, hK, hb⟩ := exists_sourceScalarBudget_positive
  refine ⟨K, hK, ?_⟩
  intro A0 hA0 a ha h0 h1 h2 N hN hsupp σ hσ J ξ
  rcases hσ with rfl | rfl
  · exact hb A0 hA0 a ha h0 h1 h2 N hN hsupp J ξ
  · obtain ⟨hc0, hc1, hc2⟩ := sourceAmplitude_conj_weighted_bounds h0 h1 h2
    have h := hb A0 hA0 (fun u => star (a u)) (sourceAmplitude_conj_contDiff ha)
      hc0 hc1 hc2 N hN (sourceAmplitude_conj_zero_above hsupp) J (-ξ)
    simpa only [sourceWindowCoefficient_neg_norm] using h

end ProofProject
