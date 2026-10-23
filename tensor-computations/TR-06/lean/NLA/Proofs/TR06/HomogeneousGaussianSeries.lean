/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual convergence of the two-sided dyadic Gaussian majorant.
-/
import NLA.Proofs.TR06.HomogeneousGaussianScaling

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open Topology
namespace NLA.Proofs.TR06.HomogeneousGaussian

/-- The large-radius dyadic Gaussian coefficients form a convergent real series. -/
theorem summable_dyadic_gaussian (q : ℕ) :
    Summable (fun n : ℕ => ((2 : ℝ) ^ n) ^ q * Real.exp (- ((2 : ℝ) ^ n) ^ 2 / 2)) := by
  let a : ℕ → ℝ := fun n => ((2 : ℝ) ^ n) ^ q * Real.exp (- ((2 : ℝ) ^ n) ^ 2 / 2)
  have hp (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    (Filter.Eventually.of_forall (fun n => ne_of_gt (hp n)))
  have heq (n : ℕ) : ‖a (n + 1)‖ / ‖a n‖ =
      (2 : ℝ) ^ q * Real.exp (- (3 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ 2) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hp _), abs_of_pos (hp _)]
    have hs : a (n+1) = ((2 : ℝ) ^ q *
        Real.exp (- (3 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ 2)) * a n := by
      dsimp [a]
      rw [pow_succ]
      have he : - ((2 : ℝ)^n * 2)^2 / 2 =
          - (3 / 2 : ℝ) * ((2 : ℝ)^n)^2 + - ((2 : ℝ)^n)^2/2 := by ring
      rw [he, Real.exp_add, mul_pow]
      ring
    rw [hs]
    exact mul_div_cancel_right₀ _ (ne_of_gt (hp n))
  simp_rw [heq]
  have hp4 : Tendsto (fun n : ℕ => ((2 : ℝ)^n)^2) atTop atTop := by
    have he (n : ℕ) : ((2 : ℝ)^n)^2 = (4 : ℝ)^n := by
      calc
        ((2 : ℝ)^n)^2 = ((2 : ℝ)^2)^n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = (4 : ℝ)^n := by norm_num
    simp_rw [he]
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have ht : Tendsto (fun n : ℕ => - (3 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ 2)
      atTop atBot := hp4.const_mul_atTop_of_neg (by norm_num)
  simpa using (Real.tendsto_exp_atBot.comp ht).const_mul ((2 : ℝ) ^ q)

/-- A single real summable majorant for both halves of the dyadic cover. -/
def dyadicCoefficient (q : ℕ) : ℤ → ℝ
  | .ofNat n => ((2 : ℝ)^n)^q * Real.exp (-((2 : ℝ)^n)^2/2)
  | .negSucc n => ((1 / 2 : ℝ)^q)^(n+1)

theorem dyadicCoefficient_nonneg (q : ℕ) (z : ℤ) : 0 ≤ dyadicCoefficient q z := by
  cases z <;> simp only [dyadicCoefficient] <;> positivity

theorem summable_dyadicCoefficient {q : ℕ} (hq : 0 < q) :
    Summable (dyadicCoefficient q) := by
  apply Summable.of_nat_of_neg_add_one
  · exact summable_dyadic_gaussian q
  · change Summable (fun n : ℕ => ((1 / 2 : ℝ)^q)^(n+1))
    have hr : (1 / 2 : ℝ)^q < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact (summable_geometric_of_lt_one (by positivity) hr).comp_injective Nat.succ_injective

theorem tsum_dyadicCoefficient_lt_top {q : ℕ} (hq : 0 < q) :
    (∑' z : ℤ, ENNReal.ofReal (dyadicCoefficient q z)) < ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (dyadicCoefficient_nonneg q)
    (summable_dyadicCoefficient hq)]
  exact ENNReal.ofReal_lt_top

#print axioms summable_dyadic_gaussian
#print axioms dyadicCoefficient_nonneg
#print axioms summable_dyadicCoefficient
#print axioms tsum_dyadicCoefficient_lt_top
#assert_trust kernel summable_dyadic_gaussian
#assert_trust kernel dyadicCoefficient_nonneg
#assert_trust kernel summable_dyadicCoefficient
#assert_trust kernel tsum_dyadicCoefficient_lt_top

end NLA.Proofs.TR06.HomogeneousGaussian
