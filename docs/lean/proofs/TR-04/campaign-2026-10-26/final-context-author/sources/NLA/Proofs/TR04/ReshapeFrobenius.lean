import NLA.Proofs.TR04.Reshape

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation

/-- Every original tensor entry appears exactly once in an unfolding sum. -/
theorem sum_unfold_indices (S : Shape) (j : Cut S) (f : Index S → ℝ) :
    (∑ a : RowIndex S j, ∑ b : ColIndex S j, f (join S j a b)) = ∑ x, f x := by
  classical
  have h := (joinEquiv S j).sum_comp f
  change (∑ p : RowIndex S j × ColIndex S j, f (join S j p.1 p.2)) = ∑ x, f x at h
  simpa only [Fintype.sum_prod_type] using h

/-- The literal tensor squared error is the squared Frobenius error of every unfolding. -/
theorem frobeniusSq_eq_unfold_sum (S : Shape) (j : Cut S) (A Y : Tensor S) :
    FrobeniusSq S A Y =
      ∑ a : RowIndex S j, ∑ b : ColIndex S j, (Unfold S A j a b - Unfold S Y j a b)^2 := by
  exact (sum_unfold_indices S j (fun x => (A x - Y x)^2)).symm

#assert_trust kernel sum_unfold_indices
#assert_trust kernel frobeniusSq_eq_unfold_sum
#print axioms frobeniusSq_eq_unfold_sum
end NLA.Proofs.TR04
