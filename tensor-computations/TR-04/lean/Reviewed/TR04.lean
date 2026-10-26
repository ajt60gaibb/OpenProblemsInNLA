/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Computation.TensorTrainApproximation
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-04: one uniform finite arithmetic/SVD program with the strict pointwise
TT approximation guarantee. The complete SVD relation and cost are concrete;
this proposition does not construct or prove a solver.
Exact specification: docs/lean/statements/TR-04/NUMERICAL_TARGETS.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.ReviewedStatements.TR04

open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

/-- One program and polynomial precede every format, rank vector, real input
and every valid SVD response trace. No favorable branch is selected. -/
def Target : Prop :=
  ∃ P : Program, ∃ C k : ℕ, 1 ≤ C ∧
    ∀ S : Shape, ∀ r : Ranks S, (∀ j, 1 ≤ r j) → ∀ A : Tensor S,
      (∃ trace : Trace P, LegalTrace P (Start P S r A) trace) ∧
      ∀ trace : Trace P, LegalTrace P (Start P S r A) trace →
        ∃ t : ℕ, ∃ X : Tensor S,
          Returns P S (trace.state t) X ∧
          CostThrough P trace t ≤ C * Size S r ^ k ∧
          Feasible S r X ∧
          (0 < Optimum S r A →
            FrobeniusSq S A X < ((S.order : ℝ) - 1) * Optimum S r A) ∧
          (Optimum S r A = 0 → X = A)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.TR04
