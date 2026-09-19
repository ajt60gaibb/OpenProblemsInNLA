import NLA.PF03.CubicArithmetic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
Finite-sum transport for the explicit cubic arithmetic. No new field instance
or evaluation oracle is assumed. Original seed mathematics: Sidney Holden,
Center for Computational Biology, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem cubicEval_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Cubic) :
    cubicEval (∑ i ∈ s, f i) = ∑ i ∈ s, cubicEval (f i) := by
  simp only [cubicEval, Finset.sum_apply, Rat.cast_sum,
    Finset.sum_add_distrib, Finset.sum_mul]

theorem cubicMul_comm (x y : Cubic) : cubicMul x y = cubicMul y x := by
  funext k
  fin_cases k <;> simp [cubicMul] <;> ring

#print axioms cubicEval_finset_sum
#assert_trust kernel cubicEval_finset_sum
#print axioms cubicMul_comm
#assert_trust kernel cubicMul_comm

end NLA.PF03
