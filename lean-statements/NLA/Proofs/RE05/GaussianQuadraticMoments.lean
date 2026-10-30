import NLA.Proofs.RE05.GaussianWick

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory

theorem gaussian_coordinate_memLp {ι : Type*} [Fintype ι] (i : ι) (p : NNReal) :
    MemLp (fun x : ι → ℝ => x i) p (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [Function.comp_def, Function.eval, id_eq] using
    (memLp_id_gaussianReal (μ := 0) (v := 1) p).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)

theorem gaussian_pair_integrable {ι : Type*} [Fintype ι] (a b : ι) :
    Integrable (fun x : ι → ℝ => x a * x b)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have ha : MemLp (fun x : ι → ℝ => x a) 2
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    simpa using gaussian_coordinate_memLp a 2
  have hb : MemLp (fun x : ι → ℝ => x b) 2
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    simpa using gaussian_coordinate_memLp b 2
  exact ha.integrable_mul hb

theorem gaussian_coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, x i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
  have h := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => x) (gaussianReal 0 1) from
      aestronglyMeasurable_id)
  simpa only [Function.comp_apply, Function.eval, gaussian_first_integral] using h

theorem gaussian_pair_integral {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    (∫ x : ι → ℝ, x a * x b ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    have h := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) a).hasLaw.integral_comp
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) by fun_prop)
    rw [gaussian_second_integral] at h
    simpa only [Function.comp_apply, Function.eval, pow_two, ↓reduceIte] using h
  · have hind := (iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
        (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)).indepFun hab
    rw [hind.integral_fun_mul_eq_mul_integral
      (gaussian_coordinate_memLp a 2).aestronglyMeasurable
      (gaussian_coordinate_memLp b 2).aestronglyMeasurable]
    simp only [gaussian_coordinate_mean, zero_mul, if_neg hab]

/-- The genuine finite quadratic form in all independent Gaussian coordinates. -/
def gaussianQuadraticForm {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

theorem gaussian_quadratic_integrable {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    Integrable (gaussianQuadraticForm A) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa only [mul_assoc] using (gaussian_pair_integrable i j).const_mul (A i j)

theorem gaussian_quadratic_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, gaussianQuadraticForm A x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = A.trace := by
  unfold gaussianQuadraticForm
  rw [integral_finsetSum]
  · calc
      _ = ∑ i, ∑ j, A i j * (if i = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc, integral_const_mul, gaussian_pair_integral]
        · intro j _
          simpa only [mul_assoc] using (gaussian_pair_integrable i j).const_mul (A i j)
      _ = A.trace := by simp [Matrix.trace, Matrix.diag, mul_ite]
  · intro i _
    apply integrable_finsetSum
    intro j _
    simpa only [mul_assoc] using (gaussian_pair_integrable i j).const_mul (A i j)

#assert_trust kernel gaussian_coordinate_memLp
#assert_trust kernel gaussian_pair_integrable
#assert_trust kernel gaussian_coordinate_mean
#assert_trust kernel gaussian_pair_integral
#assert_trust kernel gaussianQuadraticForm
#assert_trust kernel gaussian_quadratic_integrable
#assert_trust kernel gaussian_quadratic_mean
#print axioms gaussian_coordinate_memLp
#print axioms gaussian_pair_integrable
#print axioms gaussian_coordinate_mean
#print axioms gaussian_pair_integral
#print axioms gaussianQuadraticForm
#print axioms gaussian_quadratic_integrable
#print axioms gaussian_quadratic_mean
end NLA.Proofs.RE05
