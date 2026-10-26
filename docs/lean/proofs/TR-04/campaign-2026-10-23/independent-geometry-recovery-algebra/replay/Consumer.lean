import NLA.Proofs.TR04.Optimum
import NLA.Proofs.TR04.ReshapeFrobenius
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace TR04GeometryAuthorConsumer
open NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04
example (S : Shape) (j : Cut S) :
    RowIndex S j × ColIndex S j ≃ Index S := joinEquiv S j
example (S : Shape) (j : Cut S) :
    Tensor S ≃L[ℝ] Matrix (RowIndex S j) (ColIndex S j) ℝ :=
  unfoldContinuousLinearEquiv S j
example (S : Shape) (r : Ranks S) : Feasible S r 0 := feasible_zero S r
example (S : Shape) (r : Ranks S) : IsClosed {Y : Tensor S | Feasible S r Y} :=
  isClosed_feasible S r
 theorem actual_optimum_attained (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, Feasible S r X ∧ Optimum S r A = FrobeniusSq S A X :=
  exists_optimum S r A
 theorem actual_optimum_zero (S : Shape) (r : Ranks S) (A : Tensor S) :
    Optimum S r A = 0 ↔ Feasible S r A := optimum_eq_zero_iff_feasible S r A
#assert_trust kernel actual_optimum_attained
#assert_trust kernel actual_optimum_zero
#print axioms actual_optimum_attained
#print axioms actual_optimum_zero
end TR04GeometryAuthorConsumer
