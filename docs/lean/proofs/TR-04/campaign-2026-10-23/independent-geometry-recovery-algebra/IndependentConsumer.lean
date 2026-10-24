import NLA.Proofs.TR04.Optimum
import NLA.Proofs.TR04.ReshapeFrobenius
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace TR04GeometryIndependentAlgebra
open NLA.Computation.TensorTrainApproximation
 theorem actual_reshaping (S : Shape) (j : Cut S) (A Y : Tensor S) :
 FrobeniusSq S A Y = ∑ a : RowIndex S j, ∑ b : ColIndex S j,
 (Unfold S A j a b - Unfold S Y j a b)^2 :=
 NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum S j A Y
 theorem actual_rank_closed {m n : Type*} [Fintype m] [Fintype n] (r : ℕ) :
 IsClosed {M : Matrix m n ℝ | Matrix.rank M ≤ r} :=
 NLA.Proofs.TR04.isClosed_matrix_rank_le r
 theorem actual_attainment (S : Shape) (r : Ranks S) (A : Tensor S) :
 ∃ X : Tensor S, (∀ j, Matrix.rank (Unfold S X j) ≤ r j) ∧
 sInf {e : ℝ | ∃ Y : Tensor S, (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧
 e = ∑ a : Index S, (A a - Y a)^2} = ∑ a : Index S, (A a - X a)^2 :=
 NLA.Proofs.TR04.exists_optimum S r A
 theorem actual_zero (S : Shape) (r : Ranks S) (A : Tensor S) :
 Optimum S r A = 0 ↔ (∀ j, Matrix.rank (Unfold S A j) ≤ r j) :=
 NLA.Proofs.TR04.optimum_eq_zero_iff_feasible S r A
#assert_trust kernel actual_reshaping
#assert_trust kernel actual_rank_closed
#assert_trust kernel actual_attainment
#assert_trust kernel actual_zero
#print axioms actual_attainment
#print axioms actual_zero
end TR04GeometryIndependentAlgebra
