import NLA.Proofs.TR04.TTStrictOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace StrictGeometryExactConsumer
open NLA.Computation.TensorTrainApproximation
theorem actual_original_mathematics (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    (A : Tensor S) :
    ∃ X : Tensor S, (∀ j, Matrix.rank (Unfold S X j) ≤ r j) ∧
      (0 < sInf {e : ℝ | ∃ Y : Tensor S,
        (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = ∑ a, (A a - Y a)^2} →
       (∑ a, (A a - X a)^2) < ((S.order : ℝ) - 1) *
         sInf {e : ℝ | ∃ Y : Tensor S,
          (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = ∑ a, (A a - Y a)^2}) ∧
      (sInf {e : ℝ | ∃ Y : Tensor S,
        (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = ∑ a, (A a - Y a)^2} = 0 → X = A) := by
  exact NLA.Proofs.TR04.TensorFormat.TTStrict.Original.exists_strict_tensor S r hr A
#assert_trust kernel actual_original_mathematics
#print axioms actual_original_mathematics
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_svd_strict_family
#print NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_svd_strict_family
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_svd_strict_family
end StrictGeometryExactConsumer
