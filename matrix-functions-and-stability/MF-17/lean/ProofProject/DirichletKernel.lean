import Mathlib

/-!
# Elementary bounds for the finite Dirichlet polynomial

These are the pointwise estimates used by the finite sign-change construction:
the polynomial is at least `n/2` on the arc of radius `1/n`, is always at most
`n`, and is at most `π/|θ|` away from zero in the principal angular interval.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace ProofProject

/-- The one-sided Dirichlet polynomial evaluated at `e^{iθ}`. -/
def dirichletKernel (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, Complex.exp (Complex.I * (θ : ℂ)) ^ j

@[simp] lemma dirichletKernel_zero (θ : ℝ) : dirichletKernel 0 θ = 0 := by
  simp [dirichletKernel]

@[simp] lemma dirichletKernel_at_zero (n : ℕ) : dirichletKernel n 0 = n := by
  simp [dirichletKernel]

/-- Finite-index form, suitable for coefficient synthesis. -/
lemma dirichletKernel_eq_sum_fin (n : ℕ) (θ : ℝ) :
    dirichletKernel n θ = ∑ j : Fin n, Complex.exp (Complex.I * (θ : ℂ)) ^ j.val := by
  exact (Fin.sum_univ_eq_sum_range _ n).symm

/-- The kernel is a continuous trigonometric polynomial. -/
lemma continuous_dirichletKernel (n : ℕ) : Continuous (dirichletKernel n) := by
  unfold dirichletKernel
  fun_prop

/-- The triangle bound is uniform, including `n=0` and all real angles. -/
theorem norm_dirichletKernel_le (n : ℕ) (θ : ℝ) : ‖dirichletKernel n θ‖ ≤ n := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖Complex.exp (Complex.I * (θ : ℂ)) ^ j‖ := norm_sum_le _ _
    _ = n := by simp [norm_pow, Complex.norm_exp_I_mul_ofReal]

/-- Real part of an individual geometric term. -/
lemma dirichletKernel_term_re (j : ℕ) (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ)) ^ j).re = Real.cos ((j : ℝ) * θ) := by
  rw [← Complex.exp_nat_mul]
  simp [Complex.exp_re]

/-- On the short central arc, every term has real part at least one half. -/
theorem dirichletKernel_re_lower {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : |θ| ≤ 1 / (n : ℝ)) : (n : ℝ) / 2 ≤ (dirichletKernel n θ).re := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      (1 : ℝ) / 2 ≤ (Complex.exp (Complex.I * (θ : ℂ)) ^ j).re := by
    rw [dirichletKernel_term_re]
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    have harg : |(j : ℝ) * θ| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
      calc
        (j : ℝ) * |θ| ≤ (n : ℝ) * (1 / (n : ℝ)) :=
          mul_le_mul hjn hθ (abs_nonneg _) (Nat.cast_nonneg _)
        _ = 1 := by field_simp
    have hsq : ((j : ℝ) * θ) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        pow_le_pow_left₀ (abs_nonneg _) harg 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := (j : ℝ) * θ)]
  calc
    (n : ℝ) / 2 = ∑ _j ∈ Finset.range n, (1 : ℝ) / 2 := by simp; ring
    _ ≤ ∑ j ∈ Finset.range n, (Complex.exp (Complex.I * (θ : ℂ)) ^ j).re :=
      Finset.sum_le_sum hterm
    _ = (dirichletKernel n θ).re := by simp [dirichletKernel]

/-- The central-arc norm estimate used to lower-bound the weighted numerator. -/
theorem norm_dirichletKernel_lower {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : |θ| ≤ 1 / (n : ℝ)) : (n : ℝ) / 2 ≤ ‖dirichletKernel n θ‖ :=
  (dirichletKernel_re_lower hn hθ).trans (Complex.re_le_norm _)

/-- Angular reflection conjugates the finite polynomial. -/
lemma dirichletKernel_neg (n : ℕ) (θ : ℝ) :
    dirichletKernel n (-θ) = conj (dirichletKernel n θ) := by
  simp only [dirichletKernel, map_sum, map_pow, ← Complex.exp_conj]
  congr 1
  funext j
  congr 2
  simp

/-- Its norm is even in the angular variable. -/
@[simp] lemma norm_dirichletKernel_neg (n : ℕ) (θ : ℝ) :
    ‖dirichletKernel n (-θ)‖ = ‖dirichletKernel n θ‖ := by
  rw [dirichletKernel_neg, Complex.norm_conj]

/-- Jordan's inequality gives a quantitative lower bound for the geometric
sum denominator on the principal interval. -/
lemma norm_circle_exp_sub_one_lower {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    2 * |θ| / Real.pi ≤ ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf : |θ / 2| ≤ Real.pi / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hs := Real.mul_abs_le_abs_sin hhalf
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  calc
    2 * |θ| / Real.pi = 2 * (2 / Real.pi * (|θ| / 2)) := by ring
    _ ≤ 2 * |Real.sin (θ / 2)| := mul_le_mul_of_nonneg_left hs (by norm_num)

/-- Away from zero the exact geometric identity gives the inverse-angle bound. -/
theorem norm_dirichletKernel_le_pi_div {n : ℕ} {θ : ℝ}
    (hθpos : 0 < |θ|) (hθpi : |θ| ≤ Real.pi) :
    ‖dirichletKernel n θ‖ ≤ Real.pi / |θ| := by
  have hid : dirichletKernel n θ * (Complex.exp (Complex.I * (θ : ℂ)) - 1) =
      Complex.exp (Complex.I * (θ : ℂ)) ^ n - 1 :=
    geom_sum_mul _ _
  have hprod : ‖dirichletKernel n θ‖ *
      ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ 2 := by
    rw [← norm_mul, hid]
    have ht := norm_sub_le (Complex.exp (Complex.I * (θ : ℂ)) ^ n) (1 : ℂ)
    rw [norm_pow, Complex.norm_exp_I_mul_ofReal, one_pow, norm_one] at ht
    norm_num at ht
    exact ht
  have hden := norm_circle_exp_sub_one_lower hθpi
  have hsmall := mul_le_mul_of_nonneg_left hden (norm_nonneg (dirichletKernel n θ))
  have h := hsmall.trans hprod
  apply (le_div_iff₀ hθpos).mpr
  have h' := (div_le_iff₀ Real.pi_pos).mp (show
    (‖dirichletKernel n θ‖ * (2 * |θ|)) / Real.pi ≤ 2 by simpa only [mul_div_assoc] using h)
  nlinarith

/-- The two upper bounds combined in the form used by the weighted integral. -/
theorem norm_dirichletKernel_le_min {n : ℕ} {θ : ℝ}
    (hθpos : 0 < |θ|) (hθpi : |θ| ≤ Real.pi) :
    ‖dirichletKernel n θ‖ ≤ min (n : ℝ) (Real.pi / |θ|) :=
  le_min (norm_dirichletKernel_le n θ) (norm_dirichletKernel_le_pi_div hθpos hθpi)

/-- Squared form of the central-arc lower bound. -/
theorem norm_sq_dirichletKernel_lower {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : |θ| ≤ 1 / (n : ℝ)) : (n : ℝ) ^ 2 / 4 ≤ ‖dirichletKernel n θ‖ ^ 2 := by
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
    (norm_dirichletKernel_lower hn hθ) 2
  nlinarith

end ProofProject
