import NLA.Proofs.RE06.GaussianStream

/-! Exact two-sided Gaussian matrix product second moments under the finite
product law. The finite-coordinate transport is the actual original stream law. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

variable {ι : Type*} [Fintype ι]

theorem gaussian_linear_memLp (c : ι → ℝ) :
    MemLp (fun x : ι → ℝ => ∑ i, c i * x i) 2
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact memLp_finsetSum _ (fun i _ =>
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).const_mul (c i)).comp_measurePreserving
      (measurePreserving_eval _ i))

theorem gaussian_linear_mean (c : ι → ℝ) :
    ∫ x : ι → ℝ, (∑ i, c i * x i) ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0 := by
  have hi (i : ι) : Integrable (fun x : ι → ℝ => c i * x i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).const_mul (c i)).comp_measurePreserving
      (measurePreserving_eval _ i)).integrable (by norm_num)
  rw [integral_finset_sum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul]
  have he := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.integral_comp
    (show AEStronglyMeasurable (fun z : ℝ => z) (gaussianReal 0 1) from
      aestronglyMeasurable_id)
  change (∫ x : ι → ℝ, x i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = _ at he
  rw [integral_id_gaussianReal] at he
  rw [he, mul_zero]

theorem gaussian_linear_square_integrable (c : ι → ℝ) :
    Integrable (fun x : ι → ℝ => (∑ i, c i * x i) ^ 2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
  (gaussian_linear_memLp c).integrable_sq

theorem gaussian_linear_square_integral (c : ι → ℝ) :
    ∫ x : ι → ℝ, (∑ i, c i * x i) ^ 2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = ∑ i, c i ^ 2 := by
  have hv := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
    (X := fun i x => c i * x)
    (fun i => (memLp_id_gaussianReal (μ := 0) (v := 1) 2).const_mul (c i))
  have hvar : Var[fun x : ι → ℝ => ∑ i, c i * x i;
      Measure.pi (fun _ : ι => gaussianReal 0 1)] = ∑ i, c i ^ 2 := by
    simpa only [Finset.sum_apply, variance_const_mul, variance_fun_id_gaussianReal,
      NNReal.coe_one, mul_one] using hv
  rw [variance_eq_integral (gaussian_linear_memLp c).aemeasurable,
    gaussian_linear_mean c] at hvar
  simpa only [sub_zero] using hvar

/-- The actual product entry is a linear form in all independent entries. -/
theorem gaussian_product_entry {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ)
    (x : Fin b × Fin c → ℝ) (i : Fin a) (j : Fin d) :
    (U * Matrix.of (fun l k => x (l, k)) * V) i j =
      ∑ p : Fin b × Fin c, (U i p.1 * V p.2 j) * x p := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Genuine integrability holds for every rectangular shape, including empty
inner or outer dimensions. -/
theorem gaussian_product_square_integrable {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ) :
    Integrable (fun x : Fin b × Fin c → ℝ =>
      squaredFrobenius (U * Matrix.of (fun l k => x (l, k)) * V) 0)
      (Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1)) := by
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, gaussian_product_entry]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact gaussian_linear_square_integrable (fun p => U i p.1 * V p.2 j)

/-- Exact two-sided Gaussian product moment, with no rank or positivity
restriction on either fixed matrix. -/
theorem gaussian_product_square_integral {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ) :
    ∫ x : Fin b × Fin c → ℝ,
      squaredFrobenius (U * Matrix.of (fun l k => x (l, k)) * V) 0
        ∂Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1) =
      squaredFrobenius U 0 * squaredFrobenius V 0 := by
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, gaussian_product_entry]
  rw [integral_finset_sum]
  · simp_rw [integral_finset_sum _ (fun j _ =>
      gaussian_linear_square_integrable (fun p => U _ p.1 * V p.2 j)),
      gaussian_linear_square_integral, Fintype.sum_prod_type, mul_pow]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
  · intro i _
    exact integrable_finset_sum _ (fun j _ =>
      gaussian_linear_square_integrable (fun p => U i p.1 * V p.2 j))

#assert_trust kernel gaussian_linear_memLp
#assert_trust kernel gaussian_linear_mean
#assert_trust kernel gaussian_linear_square_integrable
#assert_trust kernel gaussian_linear_square_integral
#assert_trust kernel gaussian_product_entry
#assert_trust kernel gaussian_product_square_integrable
#assert_trust kernel gaussian_product_square_integral
#print axioms gaussian_linear_memLp
#print axioms gaussian_linear_mean
#print axioms gaussian_linear_square_integrable
#print axioms gaussian_linear_square_integral
#print axioms gaussian_product_entry
#print axioms gaussian_product_square_integrable
#print axioms gaussian_product_square_integral
end NLA.Proofs.RE06
