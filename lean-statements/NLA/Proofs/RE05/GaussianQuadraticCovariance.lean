import NLA.Proofs.RE05.GaussianQuadraticProduct

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory

/-- A quadratic form centered by its actual Gaussian mean. -/
def centeredGaussianQuadraticForm {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := gaussianQuadraticForm A x - A.trace

theorem gaussian_centered_quadratic_integrable {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) :
    Integrable (centeredGaussianQuadraticForm A)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
  (gaussian_quadratic_integrable A).sub (integrable_const _)

theorem gaussian_centered_quadratic_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, centeredGaussianQuadraticForm A x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
  have h := integral_sub (gaussian_quadratic_integrable A)
    (integrable_const A.trace : Integrable (fun _ : ι → ℝ => A.trace)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)))
  simpa only [centeredGaussianQuadraticForm, Pi.sub_apply, gaussian_quadratic_mean,
    integral_const, probReal_univ, one_smul, sub_self] using h

theorem gaussian_centered_product_expand {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    centeredGaussianQuadraticForm A x * centeredGaussianQuadraticForm B x =
      gaussianQuadraticForm A x * gaussianQuadraticForm B x -
        B.trace * gaussianQuadraticForm A x - A.trace * gaussianQuadraticForm B x +
        A.trace * B.trace := by
  unfold centeredGaussianQuadraticForm
  ring

theorem gaussian_centered_product_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    Integrable (fun x : ι → ℝ =>
      centeredGaussianQuadraticForm A x * centeredGaussianQuadraticForm B x)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simp_rw [gaussian_centered_product_expand]
  exact (((gaussian_quadratic_product_integrable A B).sub
    ((gaussian_quadratic_integrable A).const_mul B.trace)).sub
    ((gaussian_quadratic_integrable B).const_mul A.trace)).add (integrable_const _)

/-- Exact covariance, with no symmetry or positivity assumption. -/
theorem gaussian_centered_product_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, centeredGaussianQuadraticForm A x * centeredGaussianQuadraticForm B x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (A * B).trace + (A * B.transpose).trace := by
  have ha := gaussian_quadratic_integrable A
  have hb := gaussian_quadratic_integrable B
  have hab := gaussian_quadratic_product_integrable A B
  have h1 := integral_sub hab (ha.const_mul B.trace)
  have h2 := integral_sub (hab.sub (ha.const_mul B.trace)) (hb.const_mul A.trace)
  have h3 := integral_add ((hab.sub (ha.const_mul B.trace)).sub (hb.const_mul A.trace))
    (integrable_const (A.trace * B.trace))
  simp only [Pi.sub_apply] at h1 h2 h3
  simp_rw [gaussian_centered_product_expand]
  rw [h3, h2, h1]
  simp only [integral_const_mul, gaussian_quadratic_mean,
    gaussian_quadratic_product_integral, integral_const, probReal_univ, one_smul]
  ring

theorem real_matrix_trace_square_le_frobenius {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) : (A * A).trace ≤ (A * A.transpose).trace := by
  classical
  have hswap : (∑ i : ι, ∑ j : ι, A j i ^ 2) = ∑ i : ι, ∑ j : ι, A i j ^ 2 :=
    Finset.sum_comm
  have hbound : (∑ i : ι, ∑ j : ι, 2 * (A i j * A j i)) ≤
      ∑ i : ι, ∑ j : ι, (A i j ^ 2 + A j i ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (A i j - A j i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hbound
  rw [hswap] at hbound
  have hsum : (∑ i : ι, ∑ j : ι, A i j * A j i) ≤ ∑ i : ι, ∑ j : ι, A i j ^ 2 := by
    linarith
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    pow_two] using hsum

/-- The actual centered variance is at most twice the squared Frobenius norm. -/
theorem gaussian_centered_quadratic_variance_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, (centeredGaussianQuadraticForm A x) ^ 2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
      2 * (A * A.transpose).trace := by
  simp_rw [pow_two]
  rw [gaussian_centered_product_integral]
  linarith [real_matrix_trace_square_le_frobenius A]

#assert_trust kernel centeredGaussianQuadraticForm
#assert_trust kernel gaussian_centered_quadratic_integrable
#assert_trust kernel gaussian_centered_quadratic_mean
#assert_trust kernel gaussian_centered_product_expand
#assert_trust kernel gaussian_centered_product_integrable
#assert_trust kernel gaussian_centered_product_integral
#assert_trust kernel real_matrix_trace_square_le_frobenius
#assert_trust kernel gaussian_centered_quadratic_variance_le
#print axioms centeredGaussianQuadraticForm
#print axioms gaussian_centered_quadratic_integrable
#print axioms gaussian_centered_quadratic_mean
#print axioms gaussian_centered_product_expand
#print axioms gaussian_centered_product_integrable
#print axioms gaussian_centered_product_integral
#print axioms real_matrix_trace_square_le_frobenius
#print axioms gaussian_centered_quadratic_variance_le
end NLA.Proofs.RE05
