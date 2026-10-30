import NLA.Proofs.RE05.GaussianQuadraticMoments

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory

theorem gaussian_quadratic_product_expand {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    gaussianQuadraticForm A x * gaussianQuadraticForm B x =
      ∑ p : (ι × ι) × (ι × ι),
        (A p.1.1 p.1.2 * B p.2.1 p.2.2) *
          (x p.1.1 * x p.1.2 * x p.2.1 * x p.2.2) := by
  rw [mul_comm (gaussianQuadraticForm A x) (gaussianQuadraticForm B x)]
  simp only [gaussianQuadraticForm, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem gaussian_quadratic_product_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    Integrable (fun x : ι → ℝ => gaussianQuadraticForm A x * gaussianQuadraticForm B x)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simp_rw [gaussian_quadratic_product_expand]
  exact integrable_finsetSum _ (fun p _ =>
    (gaussian_quartic_integrable p.1.1 p.1.2 p.2.1 p.2.2).const_mul
      (A p.1.1 p.1.2 * B p.2.1 p.2.2))

theorem gaussian_wick_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (∑ p : (ι × ι) × (ι × ι),
      (A p.1.1 p.1.2 * B p.2.1 p.2.2) *
        ((if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then 1 else 0) +
          (if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then 1 else 0) +
          (if p.1.1 = p.2.2 ∧ p.1.2 = p.2.1 then 1 else 0))) =
      A.trace * B.trace + (A * B).trace + (A * B.transpose).trace := by
  classical
  have hdiag : (∑ i : ι, ∑ j : ι, A j j * B i i) =
      ∑ i : ι, ∑ j : ι, A i i * B j j := Finset.sum_comm
  simp [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib, ite_and, mul_ite,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [hdiag]
  ring

/-- Exact second joint moment of arbitrary real Gaussian quadratic forms.
Neither matrix is assumed symmetric or positive. -/
theorem gaussian_quadratic_product_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, gaussianQuadraticForm A x * gaussianQuadraticForm B x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      A.trace * B.trace + (A * B).trace + (A * B.transpose).trace := by
  simp_rw [gaussian_quadratic_product_expand]
  rw [integral_finsetSum _ (fun p _ =>
    (gaussian_quartic_integrable p.1.1 p.1.2 p.2.1 p.2.2).const_mul
      (A p.1.1 p.1.2 * B p.2.1 p.2.2))]
  simp_rw [integral_const_mul, gaussian_wick_four]
  exact gaussian_wick_contraction A B

#assert_trust kernel gaussian_quadratic_product_expand
#assert_trust kernel gaussian_quadratic_product_integrable
#assert_trust kernel gaussian_wick_contraction
#assert_trust kernel gaussian_quadratic_product_integral
#print axioms gaussian_quadratic_product_expand
#print axioms gaussian_quadratic_product_integrable
#print axioms gaussian_wick_contraction
#print axioms gaussian_quadratic_product_integral
end NLA.Proofs.RE05
