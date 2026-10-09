import ProofProject.GeneratorInversePowers

/-!
# The exponential series in powers of the negative generator inverse

The sign and factorial normalization match the normalized Gamma kernels.
The series identity itself holds for every bounded operator. For an inverse
of the full generator, the Gamma power bound gives the sharper term estimate
with a single factor `M` independent of the power.
-/

noncomputable section

namespace ProofProject

universe u

section BoundedOperator

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The two negative signs cancel inside the operator power. -/
theorem exponential_neg_power_term_eq (B : H →L[ℂ] H) (t : ℝ) (n : ℕ) :
    (((-t) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) • (-B) ^ n =
      (n.factorial : ℂ)⁻¹ • ((t : ℂ) • B) ^ n := by
  calc
    _ = (n.factorial : ℂ)⁻¹ • ((((-t : ℝ) : ℂ) • (-B)) ^ n) := by
      rw [smul_pow, smul_smul]
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.ofReal_neg, neg_smul_neg]

/-- The nonconstant exponential series with the exact coefficients used by
the weighted Gamma kernels. -/
theorem inverseEvolution_hasSum_neg_powers (B : H →L[ℂ] H) (t : ℝ) :
    HasSum (fun n : ℕ =>
      (((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) • (-B) ^ (n + 1))
      (inverseEvolution B t - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • B))
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h
  change HasSum _ (inverseEvolution B t - 1) at h
  convert h using 1
  funext n
  exact exponential_neg_power_term_eq B t (n + 1)

omit [CompleteSpace H] in
/-- The same operator series is absolutely summable in operator norm. -/
theorem summable_norm_exponential_neg_powers (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun n : ℕ =>
      ‖(((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) • (-B) ^ (n + 1)‖) := by
  have h := (summable_nat_add_iff 1).mpr
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) ((t : ℂ) • B))
  simpa only [exponential_neg_power_term_eq] using h

/-- The exact target exponential is the identity plus the normalized series. -/
theorem inverseEvolution_eq_one_add_tsum_neg_powers (B : H →L[ℂ] H) (t : ℝ) :
    inverseEvolution B t = 1 + ∑' n : ℕ,
      (((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) • (-B) ^ (n + 1) := by
  rw [(inverseEvolution_hasSum_neg_powers B t).tsum_eq]
  abel

end BoundedOperator

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {T : StableSemigroup M H} {B : H →L[ℂ] H}

/-- The genuine generator inverse has a uniform power bound, so only the
scalar exponential coefficients appear in this majorant. -/
theorem IsGeneratorInverse.norm_exponential_neg_power_term_le
    (hB : IsGeneratorInverse T B) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖(((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) • (-B) ^ (n + 1)‖ ≤
      M * (t ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  have hpow : ‖(-B) ^ (n + 1)‖ ≤ M := by
    rcases Nat.even_or_odd (n + 1) with hn | hn
    · simpa only [hn.neg_pow] using hB.pow_succ_norm_le n
    · simpa only [hn.neg_pow, norm_neg] using hB.pow_succ_norm_le n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
    abs_of_nonneg ht, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (t ^ (n + 1) / ((n + 1).factorial : ℝ)) * M :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_comm _ _

end ProofProject
