import NLA.Proofs.RE05.GaussianMoments

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory

def quarticMultiplicity {ι : Type*} [DecidableEq ι] (a b c d i : ι) : ℕ :=
  (if i = a then 1 else 0) + (if i = b then 1 else 0) +
    (if i = c then 1 else 0) + (if i = d then 1 else 0)

theorem quartic_eq_product_powers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) (x : ι → ℝ) :
    x a * x b * x c * x d = ∏ i, x i ^ quarticMultiplicity a b c d i := by
  have hsingle (e : ι) : (∏ i, x i ^ (if i = e then 1 else 0)) = x e := by
    have h := Finset.prod_eq_single e
      (s := Finset.univ) (f := fun i => x i ^ (if i = e then 1 else 0))
      (fun i _ hie => by simp [hie]) (by simp)
    exact h.trans (by simp)
  simp only [quarticMultiplicity, pow_add, Finset.prod_mul_distrib, hsingle]

theorem gaussian_quartic_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    Integrable (fun x : ι → ℝ => x a * x b * x c * x d)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [← quartic_eq_product_powers] using
    gaussian_product_powers_integrable (quarticMultiplicity a b c d)

/-- Wick's fourth-moment formula for the literal finite product of standard
real Gaussians, including every repeated-coordinate case. -/
theorem gaussian_wick_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    (∫ x : ι → ℝ, x a * x b * x c * x d
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (if a = b ∧ c = d then 1 else 0) +
        (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) := by
  classical
  rw [show (fun x : ι → ℝ => x a * x b * x c * x d) =
      (fun x => ∏ i, x i ^ quarticMultiplicity a b c d i) by
        funext x; exact quartic_eq_product_powers a b c d x]
  rw [gaussian_product_powers_integral]
  let S : Finset ι := {a, b, c, d}
  have hS : (∏ i : ι, ∫ x : ℝ, x ^ quarticMultiplicity a b c d i ∂gaussianReal 0 1) =
      ∏ i ∈ S, ∫ x : ℝ, x ^ quarticMultiplicity a b c d i ∂gaussianReal 0 1 := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have ha : i ≠ a := by intro h; apply hi; simp [S, h]
    have hb : i ≠ b := by intro h; apply hi; simp [S, h]
    have hc : i ≠ c := by intro h; apply hi; simp [S, h]
    have hd : i ≠ d := by intro h; apply hi; simp [S, h]
    simp [quarticMultiplicity, ha, hb, hc, hd]
  rw [hS]
  clear hS
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;> by_cases hcd : c = d <;>
    simp_all [S, quarticMultiplicity, eq_comm, gaussian_second_integral,
      gaussian_third_integral, gaussian_fourth_integral]
  all_goals norm_num

#assert_trust kernel quarticMultiplicity
#assert_trust kernel quartic_eq_product_powers
#assert_trust kernel gaussian_quartic_integrable
#assert_trust kernel gaussian_wick_four
#print axioms quarticMultiplicity
#print axioms quartic_eq_product_powers
#print axioms gaussian_quartic_integrable
#print axioms gaussian_wick_four
end NLA.Proofs.RE05
