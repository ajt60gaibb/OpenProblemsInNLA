import NLA.Proofs.IE22.GaussianBasics

/-! Actual relative norm-square moments and tail bounds for standard Gaussian
vectors. The finite scalar square variance is retained symbolically. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22

theorem gaussian_relative_norm_square_memLp (n : ℕ) :
    MemLp (fun g : Euclid n => ‖g‖ ^ 2 / (n : ℝ) - 1) 2
      (stdGaussian (Euclid n)) := by
  convert ((gaussian_norm_square_memLp n).mul_const ((n : ℝ)⁻¹)).sub
    (memLp_const (1 : ℝ)) using 1
  ext g
  simp only [Pi.sub_apply, div_eq_mul_inv]

theorem gaussian_relative_norm_square_mean {n : ℕ} (hn : 0 < n) :
    (∫ g : Euclid n, (‖g‖ ^ 2 / (n : ℝ) - 1) ∂stdGaussian (Euclid n)) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [integral_sub]
  · rw [integral_div, gaussian_norm_square_mean]
    simp [hnR]
  · simpa only [div_eq_mul_inv] using
      ((gaussian_norm_square_memLp n).mul_const ((n : ℝ)⁻¹)).integrable (by norm_num)
  · exact integrable_const _

theorem gaussian_relative_norm_square_variance {n : ℕ} (hn : 0 < n) :
    Var[(fun g : Euclid n => ‖g‖ ^ 2 / (n : ℝ) - 1); stdGaussian (Euclid n)] =
      normalSquareVariance / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [variance_sub_const (by fun_prop)]
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, gaussian_norm_square_variance]
  field_simp

theorem gaussian_relative_norm_square_second_moment {n : ℕ} (hn : 0 < n) :
    (∫ g : Euclid n, (‖g‖ ^ 2 / (n : ℝ) - 1) ^ 2 ∂stdGaussian (Euclid n)) =
      normalSquareVariance / (n : ℝ) := by
  have h := variance_eq_integral (gaussian_relative_norm_square_memLp n).aemeasurable
  rw [gaussian_relative_norm_square_mean hn] at h
  simp only [sub_zero] at h
  exact h.symm.trans (gaussian_relative_norm_square_variance hn)

theorem gaussian_relative_norm_square_chebyshev {n : ℕ} (hn : 0 < n)
    (δ : ℝ) (hδ : 0 < δ) :
    stdGaussian (Euclid n) {g | δ ≤ |‖g‖ ^ 2 / (n : ℝ) - 1|} ≤
      ENNReal.ofReal (normalSquareVariance / ((n : ℝ) * δ ^ 2)) := by
  have h := meas_ge_le_variance_div_sq (gaussian_relative_norm_square_memLp n) hδ
  rw [gaussian_relative_norm_square_mean hn, gaussian_relative_norm_square_variance hn] at h
  simpa only [sub_zero, div_div] using h

theorem gaussian_small_norm_probability {n : ℕ} (hn : 0 < n) :
    stdGaussian (Euclid n) {g | ‖g‖ ^ 2 / (n : ℝ) < 1 / 2} ≤
      ENNReal.ofReal (4 * normalSquareVariance / (n : ℝ)) := by
  have hsubset : {g : Euclid n | ‖g‖ ^ 2 / (n : ℝ) < 1 / 2} ⊆
      {g : Euclid n | (1 / 2 : ℝ) ≤ |‖g‖ ^ 2 / (n : ℝ) - 1|} := by
    intro g hg
    change 1 / 2 ≤ |‖g‖ ^ 2 / (n : ℝ) - 1|
    have h := neg_le_abs (‖g‖ ^ 2 / (n : ℝ) - 1)
    change ‖g‖ ^ 2 / (n : ℝ) < 1 / 2 at hg
    linarith
  have h := (measure_mono hsubset).trans
    (gaussian_relative_norm_square_chebyshev hn (1 / 2) (by norm_num))
  have halg : normalSquareVariance / ((n : ℝ) * (1 / 2 : ℝ) ^ 2) =
      4 * normalSquareVariance / (n : ℝ) := by ring
  simpa only [halg] using h

#assert_trust kernel gaussian_relative_norm_square_memLp
#assert_trust kernel gaussian_relative_norm_square_mean
#assert_trust kernel gaussian_relative_norm_square_variance
#assert_trust kernel gaussian_relative_norm_square_second_moment
#assert_trust kernel gaussian_relative_norm_square_chebyshev
#assert_trust kernel gaussian_small_norm_probability
#print axioms gaussian_relative_norm_square_memLp
#print axioms gaussian_relative_norm_square_mean
#print axioms gaussian_relative_norm_square_variance
#print axioms gaussian_relative_norm_square_second_moment
#print axioms gaussian_relative_norm_square_chebyshev
#print axioms gaussian_small_norm_probability
end NLA.Proofs.IE22
