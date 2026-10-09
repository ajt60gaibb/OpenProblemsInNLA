import Mathlib

/-!
# Passing a polynomial bound from a smaller circle to the unit circle

The reflected polynomial is holomorphic at the origin, so the maximum-modulus
principle applies without any puncture or removable-singularity argument.
The degree bound can be padded, and both degree zero and radius one are allowed.
-/

noncomputable section

namespace ProofProject

open Polynomial Metric Set

private lemma polynomial_reflect_eval_inv (p : Polynomial ℂ) (d : ℕ)
    (hd : p.natDegree ≤ d) {z : ℂ} (hz : z ≠ 0) :
    (reflect d p).eval z = z ^ d * p.eval z⁻¹ := by
  let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have he := eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ d p hd
  change (reflect d p).eval (⅟(z⁻¹)) * (z⁻¹) ^ d = p.eval z⁻¹ at he
  rw [invOf_eq_inv, inv_inv] at he
  calc
    _ = (reflect d p).eval z * ((z⁻¹) ^ d * z ^ d) := by
      rw [← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]
    _ = p.eval z⁻¹ * z ^ d := by rw [← mul_assoc, he]
    _ = _ := mul_comm _ _

/-- A degree-d polynomial loses at most the factor r^(-d) when passing from
the circle of positive radius r to the unit circle. -/
theorem polynomial_radial_maximum (h : Polynomial ℂ) {d : ℕ} (hd : h.natDegree ≤ d)
    {r A : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ w : ℂ, ‖w‖ = r → ‖h.eval w‖ ≤ A) {z : ℂ} (hz : ‖z‖ = 1) :
    r ^ d * ‖h.eval z‖ ≤ A := by
  let P : Polynomial ℂ := h.comp (C (r : ℂ) * X)
  let R : Polynomial ℂ := reflect d P
  have hPdeg : P.natDegree ≤ d := by
    calc
      _ ≤ h.natDegree * (C (r : ℂ) * X).natDegree := natDegree_comp_le
      _ ≤ h.natDegree * 1 := Nat.mul_le_mul_left _
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      _ ≤ d := by simpa only [mul_one] using hd
  have hRbound : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖R.eval w‖ ≤ A := by
    intro w hw
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := closedBall (0 : ℂ) 1) isBounded_closedBall R.differentiable.diffContOnCl
    · intro ζ hζ
      have hζnorm : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp (frontier_closedBall_subset_sphere hζ)
      have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζnorm]; norm_num)
      calc
        _ = ‖ζ ^ d * P.eval ζ⁻¹‖ := congrArg norm (polynomial_reflect_eval_inv P d hPdeg hζ0)
        _ = ‖P.eval ζ⁻¹‖ := by rw [norm_mul, norm_pow, hζnorm, one_pow, one_mul]
        _ = ‖h.eval ((r : ℂ) * ζ⁻¹)‖ := by simp only [P, eval_comp, eval_mul, eval_C, eval_X]
        _ ≤ A := hbound _ (by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
            norm_inv, hζnorm, inv_one, mul_one])
    · simpa only [isClosed_closedBall.closure_eq, mem_closedBall_zero_iff] using hw
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hξ : ‖(r : ℂ) / z‖ = r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hz, div_one]
  have heval : R.eval ((r : ℂ) / z) = ((r : ℂ) / z) ^ d * h.eval z := by
    rw [show R = reflect d P from rfl, polynomial_reflect_eval_inv P d hPdeg (div_ne_zero hrc hz0)]
    simp only [P, eval_comp, eval_mul, eval_C, eval_X]
    congr 2
    field_simp [hrc, hz0]
  have hnorm := congrArg norm heval
  rw [norm_mul, norm_pow, hξ] at hnorm
  rw [← hnorm]
  exact hRbound _ (hξ.trans_le hr1)

theorem polynomial_radial_maximum_div (h : Polynomial ℂ) {d : ℕ} (hd : h.natDegree ≤ d)
    {r A : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ w : ℂ, ‖w‖ = r → ‖h.eval w‖ ≤ A) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖h.eval z‖ ≤ A / r ^ d := by
  apply (le_div_iff₀ (pow_pos hr0 d)).mpr
  simpa only [mul_comm] using polynomial_radial_maximum h hd hr0 hr1 hbound hz

/-- Applying the polynomial maximum lemma to h*h gives the squared-norm
version directly, without introducing a square root of the upper bound. -/
theorem polynomial_radial_maximum_sq (h : Polynomial ℂ) {d : ℕ} (hd : h.natDegree ≤ d)
    {r A : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ w : ℂ, ‖w‖ = r → ‖h.eval w‖ ^ 2 ≤ A) {z : ℂ} (hz : ‖z‖ = 1) :
    r ^ (2 * d) * ‖h.eval z‖ ^ 2 ≤ A := by
  have hdeg : (h * h).natDegree ≤ 2 * d :=
    natDegree_mul_le.trans (by omega)
  have hb : ∀ w : ℂ, ‖w‖ = r → ‖(h * h).eval w‖ ≤ A := by
    intro w hw
    simpa only [eval_mul, norm_mul, pow_two] using hbound w hw
  simpa only [eval_mul, norm_mul, pow_two] using
    polynomial_radial_maximum (h * h) hdeg hr0 hr1 hb hz

theorem polynomial_radial_maximum_sq_inv (h : Polynomial ℂ) {d : ℕ} (hd : h.natDegree ≤ d)
    {r A : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ w : ℂ, ‖w‖ = r → ‖h.eval w‖ ^ 2 ≤ A) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖h.eval z‖ ^ 2 ≤ r⁻¹ ^ (2 * d) * A := by
  have he : ‖h.eval z‖ ^ 2 ≤ A / r ^ (2 * d) := by
    apply (le_div_iff₀ (pow_pos hr0 _)).mpr
    simpa only [mul_comm] using polynomial_radial_maximum_sq h hd hr0 hr1 hbound hz
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using he

/-- The source radius choice costs at most exp(2) in squared polynomial norm. -/
lemma source_radius_inverse_pow_le_exp_two {n d : ℕ} (hn : 2 ≤ n) (hd : d ≤ n - 1) :
    (1 - 1 / (n : ℝ))⁻¹ ^ (2 * d) ≤ Real.exp 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have heq : (1 - 1 / (n : ℝ))⁻¹ = 1 + ((n - 1 : ℕ) : ℝ)⁻¹ := by
    rw [hcast]
    have hfrac : 1 - 1 / (n : ℝ) = ((n : ℝ) - 1) / n := by field_simp [hn0]
    rw [hfrac, inv_div]
    field_simp [hn1]
    ring
  rw [heq]
  have hb : 1 ≤ 1 + ((n - 1 : ℕ) : ℝ)⁻¹ :=
    le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have he : (1 + ((n - 1 : ℕ) : ℝ)⁻¹) ^ d ≤ Real.exp 1 :=
    (pow_le_pow_right₀ hb hd).trans Real.one_add_inv_pow_le_exp
  calc
    _ = ((1 + ((n - 1 : ℕ) : ℝ)⁻¹) ^ d) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by positivity) he 2
    _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num

end ProofProject
