import NLA.Proofs.RE05.GaussianWick
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory NLA.Proofs.RE05

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) (x : ι → ℝ) :
    x a * x b * x c * x d = ∏ i, x i ^ quarticMultiplicity a b c d i :=
  quartic_eq_product_powers a b c d x
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) :
    Integrable (fun x : ι → ℝ => x a * x b * x c * x d)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := gaussian_quartic_integrable a b c d
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) :
    (∫ x : ι → ℝ, x a * x b * x c * x d
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (if a = b ∧ c = d then 1 else 0) +
        (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) :=
  gaussian_wick_four a b c d
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    (∫ x : ι → ℝ, x a * x a * x a * x a
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 3 := by
  have h := gaussian_wick_four a a a a
  norm_num at h
  exact h
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (hab : a ≠ b) :
    (∫ x : ι → ℝ, x a * x b * x a * x b
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 1 := by
  simpa [hab, Ne.symm hab] using gaussian_wick_four a b a b

#assert_trust kernel quarticMultiplicity
#assert_trust kernel quartic_eq_product_powers
#assert_trust kernel gaussian_quartic_integrable
#assert_trust kernel gaussian_wick_four
#print axioms quarticMultiplicity
#print axioms quartic_eq_product_powers
#print axioms gaussian_quartic_integrable
#print axioms gaussian_wick_four
