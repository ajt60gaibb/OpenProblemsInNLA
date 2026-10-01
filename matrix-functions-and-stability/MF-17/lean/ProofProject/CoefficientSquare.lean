import ProofProject.ReplicationBound

/-!
# Completing the square in the coefficient deficit

The complex Hilbert inner product is conjugate linear in its first argument.
The explicitly attained coefficient minimum controls every interior multiplier
with the precise source constant `(M^4+1)/(M^2-1)`.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The positive quadratic coefficient for a contractive multiplier. -/
def coefficientSquareK (M : ℝ) (z : ℂ) : ℝ := M ^ 2 - ‖z‖ ^ 2

/-- The linear coefficient, in Mathlib's first-argument conjugate convention. -/
def coefficientSquareB (M : ℝ) (v y e : H) (z : ℂ) : ℂ :=
  (M ^ 2 : ℝ) * inner ℂ e v - star z * inner ℂ e y

/-- The exact minimizer of the coefficient deficit. -/
def coefficientMinimizer (M : ℝ) (v y e : H) (z : ℂ) : ℂ :=
  -coefficientSquareB M v y e z / (coefficientSquareK M z : ℂ)

lemma coefficientSquareK_pos {M : ℝ} (hM : 1 < M) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 < coefficientSquareK M z := by
  have hzsq := pow_le_pow_left₀ (norm_nonneg z) hz 2
  unfold coefficientSquareK
  nlinarith

lemma coefficientMinimizer_zero {M : ℝ} (hM : 1 < M) (v y e : H) :
    coefficientMinimizer M v y e 0 = -inner ℂ e v := by
  have hM0 : M ≠ 0 := by linarith
  have hMc : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM0
  simp only [coefficientMinimizer, coefficientSquareB, coefficientSquareK,
    star_zero, zero_mul, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Complex.ofReal_pow]
  field_simp

lemma coefficientMinimizer_one_stationary {M : ℝ} (hM : 1 < M) (v y e : H) :
    (M ^ 2 : ℝ) * (inner ℂ e v + coefficientMinimizer M v y e 1) =
      inner ℂ e y + coefficientMinimizer M v y e 1 := by
  have hden : (M : ℂ) ^ 2 - 1 ≠ 0 := by
    have hr : M ^ 2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast hr
  simp only [coefficientMinimizer, coefficientSquareB, coefficientSquareK,
    star_one, one_mul, norm_one, one_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow]
  field_simp
  ring

/-- The deficit is an ordinary positive complex quadratic. -/
lemma coefficientDeficit_eq_quadratic (M : ℝ) (v y e : H) (he : ‖e‖ = 1) (t z : ℂ) :
    coefficientDeficit M v y e t z = M ^ 2 * ‖v‖ ^ 2 - ‖y‖ ^ 2 +
      coefficientSquareK M z * ‖t‖ ^ 2 +
      2 * (star t * coefficientSquareB M v y e z).re := by
  rw [coefficientDeficit, norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ)]
  simp only [inner_smul_right, norm_smul, he, mul_one, norm_mul, mul_pow]
  rw [← inner_conj_symm (𝕜 := ℂ) v e, ← inner_conj_symm (𝕜 := ℂ) y e]
  simp only [coefficientSquareK, coefficientSquareB, RCLike.re_to_complex,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Scalar completion of the square, with a positive real leading coefficient. -/
lemma complex_quadratic_complete_square {k : ℝ} (hk : 0 < k) (b t : ℂ) :
    k * ‖t‖ ^ 2 + 2 * (star t * b).re =
      -‖b‖ ^ 2 / k + k * ‖t - (-b / (k : ℂ))‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- The exact minimized value of the coefficient deficit. -/
theorem coefficientDeficit_minimum_value {M : ℝ} (hM : 1 < M) (v y e : H)
    (he : ‖e‖ = 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    coefficientDeficit M v y e (coefficientMinimizer M v y e z) z =
      M ^ 2 * ‖v‖ ^ 2 - ‖y‖ ^ 2 -
        ‖coefficientSquareB M v y e z‖ ^ 2 / coefficientSquareK M z := by
  rw [coefficientDeficit_eq_quadratic M v y e he]
  rw [add_assoc, complex_quadratic_complete_square (coefficientSquareK_pos hM hz)]
  simp [coefficientMinimizer]
  ring

/-- Every coefficient is the attained minimum plus a nonnegative square. -/
theorem coefficientDeficit_complete_square {M : ℝ} (hM : 1 < M) (v y e : H)
    (he : ‖e‖ = 1) (t : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    coefficientDeficit M v y e t z =
      coefficientDeficit M v y e (coefficientMinimizer M v y e z) z +
        coefficientSquareK M z * ‖t - coefficientMinimizer M v y e z‖ ^ 2 := by
  rw [coefficientDeficit_minimum_value hM v y e he hz,
    coefficientDeficit_eq_quadratic M v y e he]
  rw [add_assoc, complex_quadratic_complete_square (coefficientSquareK_pos hM hz)]
  simp only [coefficientMinimizer]
  ring

/-- The explicit minimizing coefficient gives a lower bound for every input. -/
theorem coefficientDeficit_minimum_le {M : ℝ} (hM : 1 < M) (v y e : H)
    (he : ‖e‖ = 1) (t : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    coefficientDeficit M v y e (coefficientMinimizer M v y e z) z ≤
      coefficientDeficit M v y e t z := by
  rw [coefficientDeficit_complete_square hM v y e he t hz]
  exact le_add_of_nonneg_right (mul_nonneg (coefficientSquareK_pos hM hz).le (sq_nonneg _))

/-- Two-term Cauchy--Schwarz gives the precise numerator in the source bound. -/
lemma coefficientSquareB_norm_sq_le (M : ℝ) (v y e : H) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖coefficientSquareB M v y e z‖ ^ 2 ≤
      (M ^ 4 + 1) * (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) := by
  have hnorm : ‖coefficientSquareB M v y e z‖ ≤
      M ^ 2 * ‖inner ℂ e v‖ + ‖inner ℂ e y‖ := by
    unfold coefficientSquareB
    calc
      _ ≤ ‖(M ^ 2 : ℝ) * inner ℂ e v‖ + ‖star z * inner ℂ e y‖ := norm_sub_le _ _
      _ = M ^ 2 * ‖inner ℂ e v‖ + ‖z‖ * ‖inner ℂ e y‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := add_le_add le_rfl (by simpa using mul_le_mul_of_nonneg_right hz (norm_nonneg _))
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg (‖inner ℂ e v‖ - M ^ 2 * ‖inner ℂ e y‖)]

/-- All interior multipliers have a uniform lower deficit controlled solely by
the two correlations; the constant is exactly the one in the source. -/
theorem coefficientDeficit_interior_lower {M : ℝ} (hM : 1 < M) (v y e : H)
    (he : ‖e‖ = 1) (hvy : ‖y‖ ≤ M * ‖v‖) (t : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    -((M ^ 4 + 1) / (M ^ 2 - 1)) *
      (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) ≤ coefficientDeficit M v y e t z := by
  have hden : 0 < M ^ 2 - 1 := by nlinarith
  have hk := coefficientSquareK_pos hM hz
  have hdenle : M ^ 2 - 1 ≤ coefficientSquareK M z := by
    have hzsq := pow_le_pow_left₀ (norm_nonneg z) hz 2
    unfold coefficientSquareK
    nlinarith
  have hbase : 0 ≤ M ^ 2 * ‖v‖ ^ 2 - ‖y‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hvy 2
    nlinarith
  have hratio : ‖coefficientSquareB M v y e z‖ ^ 2 / coefficientSquareK M z ≤
      ((M ^ 4 + 1) / (M ^ 2 - 1)) *
        (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) := by
    calc
      _ ≤ ((M ^ 4 + 1) * (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2)) /
          coefficientSquareK M z :=
        div_le_div_of_nonneg_right (coefficientSquareB_norm_sq_le M v y e hz) hk.le
      _ ≤ ((M ^ 4 + 1) * (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2)) / (M ^ 2 - 1) :=
        div_le_div_of_nonneg_left (by positivity) hden hdenle
      _ = _ := by ring
  have hmin := coefficientDeficit_minimum_le hM v y e he t hz
  rw [coefficientDeficit_minimum_value hM v y e he hz] at hmin
  nlinarith

end ProofProject
