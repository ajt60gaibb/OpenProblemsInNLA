import Mathlib

/-!
# Power integrals for the weighted Dirichlet-kernel estimates

These are the scalar integral estimates used in the lower construction. The
singularity at zero is Lebesgue integrable when its exponent is greater than
`-1`; no value assigned at the endpoint affects the integrals. Positive real
scales are allowed, so the statements apply in particular to integer degrees.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

/-- The singular numerator weight is integrable right up to zero. -/
lemma intervalIntegrable_singular_power {α : ℝ} (hα : α < 1) (b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => θ ^ (-α)) volume 0 b :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

/-- The corresponding ordinary Lebesgue integrability on the open interval. -/
lemma integrableOn_singular_power {α b : ℝ} (hα : α < 1) (hb : 0 < b) :
    IntegrableOn (fun θ : ℝ => θ ^ (-α)) (Set.Ioo 0 b) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr (by linarith)

/-- The denominator's near-zero weight is also integrable. -/
lemma intervalIntegrable_positive_power {α : ℝ} (hα : 0 < α) (b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => θ ^ α) volume 0 b :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

/-- Away from zero there is no restriction on the power exponent. -/
lemma intervalIntegrable_power_tail (α : ℝ) {n : ℝ} (hn : 0 < n) :
    IntervalIntegrable (fun θ : ℝ => θ ^ (α - 2)) volume (1 / n) 1 :=
  intervalIntegral.intervalIntegrable_rpow (Or.inr
    (Set.notMem_uIcc_of_lt (one_div_pos.mpr hn) zero_lt_one))

/-- A scaled integral at the inverse degree, with the general exponent. -/
theorem scaled_small_power_integral {s n : ℝ} (hs : -1 < s) (hn : 0 < n) :
    n ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / n), θ ^ s) = n ^ (1 - s) / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.zero_rpow (by linarith), sub_zero]
  have hp : n ^ 2 * (1 / n) ^ (s + 1) = n ^ (1 - s) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_two, ← Real.rpow_add hn]
    congr 1
    ring
  rw [← mul_div_assoc, hp]

/-- Exact growth of the singular-power part of the numerator lower bound. -/
theorem dirichlet_numerator_power_integral {α n : ℝ} (hα : α < 1) (hn : 0 < n) :
    n ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / n), θ ^ (-α)) =
      n ^ (1 + α) / (1 - α) := by
  simpa only [sub_neg_eq_add, neg_add_eq_sub] using
    scaled_small_power_integral (s := -α) (by linarith) hn

/-- Exact growth of the near-zero contribution to the denominator upper bound. -/
theorem dirichlet_denominator_small_integral {α n : ℝ}
    (hα : 0 < α) (hn : 0 < n) :
    n ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / n), θ ^ α) =
      n ^ (1 - α) / (1 + α) := by
  simpa only [add_comm α 1] using scaled_small_power_integral (by linarith : -1 < α) hn

/-- Exact tail contribution. The antiderivative is applied only away from zero. -/
theorem dirichlet_denominator_tail_integral {α n : ℝ}
    (hα : α < 1) (hn : 0 < n) :
    (∫ θ : ℝ in (1 / n)..1, θ ^ (α - 2)) =
      (n ^ (1 - α) - 1) / (1 - α) := by
  rw [integral_rpow (Or.inr ⟨by linarith,
    Set.notMem_uIcc_of_lt (one_div_pos.mpr hn) zero_lt_one⟩)]
  have he : α - 2 + 1 = -(1 - α) := by ring
  rw [he, Real.one_rpow, one_div, ← Real.rpow_neg_eq_inv_rpow, neg_neg]
  field_simp [show 1 - α ≠ 0 by linarith]
  ring

/-- The two denominator contributions have the required power growth. -/
theorem dirichlet_denominator_power_integral_le {α n : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hn : 0 < n) :
    n ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / n), θ ^ α) +
      (∫ θ : ℝ in (1 / n)..1, θ ^ (α - 2)) ≤
        (1 / (1 + α) + 1 / (1 - α)) * n ^ (1 - α) := by
  rw [dirichlet_denominator_small_integral hα0 hn,
    dirichlet_denominator_tail_integral hα1 hn]
  have htail : (n ^ (1 - α) - 1) / (1 - α) ≤ n ^ (1 - α) / (1 - α) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc
    _ ≤ n ^ (1 - α) / (1 + α) + n ^ (1 - α) / (1 - α) := add_le_add_right htail _
    _ = _ := by ring

/-- Integer-degree version of the numerator identity. -/
theorem dirichlet_numerator_power_integral_nat {α : ℝ} (hα : α < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ (-α)) =
      (n : ℝ) ^ (1 + α) / (1 - α) :=
  dirichlet_numerator_power_integral hα (by exact_mod_cast (show 0 < n by omega))

/-- Integer-degree version of the combined denominator estimate. -/
theorem dirichlet_denominator_power_integral_nat_le {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ α) +
      (∫ θ : ℝ in (1 / (n : ℝ))..1, θ ^ (α - 2)) ≤
        (1 / (1 + α) + 1 / (1 - α)) * (n : ℝ) ^ (1 - α) :=
  dirichlet_denominator_power_integral_le hα0 hα1
    (by exact_mod_cast (show 0 < n by omega))

end ProofProject
