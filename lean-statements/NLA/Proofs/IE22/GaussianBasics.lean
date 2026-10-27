import Mathlib
import NLA.Statements.IE22

/-! Actual standard Gaussian laws and finite scalar moments used by both
halves of the qualitative sharp-constant proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22

abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

def normalSquareVariance : ℝ := Var[(fun z : ℝ => z ^ 2); gaussianReal 0 1]

def normalFourthMoment : ℝ := ∫ z : ℝ, z ^ 4 ∂gaussianReal 0 1

theorem normalSquareVariance_nonneg : 0 ≤ normalSquareVariance :=
  variance_nonneg _ _

theorem normalFourthMoment_nonneg : 0 ≤ normalFourthMoment :=
  integral_nonneg (fun z => by positivity)

theorem normal_fourth_integrable : Integrable (fun z : ℝ => z ^ 4) (gaussianReal 0 1) := by
  have hp := memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num)
  have h := hp.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)
  have habs (z : ℝ) : ‖z‖ ^ 4 = z ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.norm_eq_abs, sq_abs, ← pow_mul]
  simpa only [id_eq, habs] using h

theorem normal_square_memLp : MemLp (fun z : ℝ => z ^ 2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  convert normal_fourth_integrable using 1
  ext z
  ring

theorem normal_square_integrable : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) :=
  normal_square_memLp.integrable (by norm_num)

theorem normal_second_moment : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num))
  simpa only [variance_id_gaussianReal, integral_id_gaussianReal, Pi.pow_apply, id_eq,
    zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, NNReal.coe_one] using h.symm

theorem gaussian_inner_mean {n : ℕ} (v : Euclid n) :
    (∫ g : Euclid n, inner ℝ v g ∂stdGaussian (Euclid n)) = 0 := by
  have hi : Integrable (id : Euclid n → Euclid n) (stdGaussian (Euclid n)) :=
    IsGaussian.integrable_id
  have h := (innerSL ℝ v).integral_comp_comm hi
  simpa only [integral_id_stdGaussian, map_zero, id_eq, innerSL_apply_apply] using h

theorem gaussian_inner_variance {n : ℕ} (v : Euclid n) :
    Var[(fun g : Euclid n => inner ℝ v g); stdGaussian (Euclid n)] = ‖v‖ ^ 2 := by
  simpa only [coe_innerSL_apply, innerSL_apply_norm] using
    variance_dual_stdGaussian (innerSL ℝ v)

theorem gaussian_unit_inner_law {n : ℕ} (v : Euclid n) (hv : ‖v‖ = 1) :
    (stdGaussian (Euclid n)).map (fun g => inner ℝ v g) = gaussianReal 0 1 := by
  have hgauss := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (Euclid n))).map_fun
    (innerSL ℝ v)
  have h := hgauss.map_eq_gaussianReal
  simpa only [innerSL_apply_apply, id_eq, gaussian_inner_mean, gaussian_inner_variance, hv,
    one_pow, Real.toNNReal_one] using h

theorem gaussian_norm_sq_eq_sum {n : ℕ} (g : Euclid n) :
    ‖g‖ ^ 2 = ∑ i : Fin n, (g i) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq g

theorem gaussian_norm_square_memLp (n : ℕ) :
    MemLp (fun g : Euclid n => ‖g‖ ^ 2) 2 (stdGaussian (Euclid n)) := by
  have hp : MemLp (id : Euclid n → Euclid n) 4 (stdGaussian (Euclid n)) :=
    IsGaussian.memLp_id _ _ (by norm_num)
  have h := hp.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  convert h using 1
  ext g
  simp only [id_eq]
  ring

theorem gaussian_norm_square_mean (n : ℕ) :
    (∫ g : Euclid n, ‖g‖ ^ 2 ∂stdGaussian (Euclid n)) = (n : ℝ) := by
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [gaussian_norm_sq_eq_sum]
  change (∫ g : Fin n → ℝ, ∑ i : Fin n, (g i) ^ 2
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = (n : ℝ)
  rw [integral_finsetSum]
  · calc
      _ = ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1)
          (i := i) normal_square_integrable.aestronglyMeasurable]
        exact normal_second_moment
      _ = (n : ℝ) := by simp
  · intro i _
    exact (normal_square_memLp.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).integrable (by norm_num)

theorem gaussian_norm_square_variance (n : ℕ) :
    Var[(fun g : Euclid n => ‖g‖ ^ 2); stdGaussian (Euclid n)] =
      (n : ℝ) * normalSquareVariance := by
  rw [← map_pi_eq_stdGaussian]
  rw [variance_map (by fun_prop) (by fun_prop)]
  have hsum : (fun g : Euclid n => ‖g‖ ^ 2) ∘ (WithLp.toLp 2) =
      ∑ i : Fin n, (fun g : Fin n → ℝ => (g i) ^ 2) := by
    ext g
    simpa only [Function.comp_apply, Finset.sum_apply] using
      gaussian_norm_sq_eq_sum (WithLp.toLp 2 g : Euclid n)
  rw [hsum, variance_sum_pi (fun _ => normal_square_memLp)]
  simp [normalSquareVariance]

#assert_trust kernel normal_square_memLp
#assert_trust kernel normal_fourth_integrable
#assert_trust kernel normal_second_moment
#assert_trust kernel gaussian_inner_mean
#assert_trust kernel gaussian_inner_variance
#assert_trust kernel gaussian_unit_inner_law
#assert_trust kernel gaussian_norm_sq_eq_sum
#assert_trust kernel gaussian_norm_square_memLp
#assert_trust kernel gaussian_norm_square_mean
#assert_trust kernel gaussian_norm_square_variance
#print axioms normal_second_moment
#print axioms gaussian_unit_inner_law
#print axioms gaussian_norm_square_variance
end NLA.Proofs.IE22
