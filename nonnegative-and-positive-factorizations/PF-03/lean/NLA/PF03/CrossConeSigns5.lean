import NLA.PF03.ConeNumericalAlgebra

/-!
C10 internal signs for lower group 5. Only literal upper groups enter the
kernel arithmetic. The arbitrary Fin index is dispatched by its Nat value
after the strict-order hypothesis and the Fin bound have been used.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace NLA.PF03

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cross_cone_lower_pair_5_6 (a b : Fin 3) :
    0 < cubicLower (crossCubic 5 6 a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem cross_cone_lower5 (j : Fin 7) (hij : (5 : Fin 7) < j) (a b : Fin 3) :
    0 < cubicLower (crossCubic 5 j a b) := by
  change 5 < j.val at hij
  have hjbound : j.val < 7 := j.isLt
  have hjval : j.val = 6 := by omega
  have hj : j = (6 : Fin 7) := Fin.ext hjval
  subst j
  exact cross_cone_lower_pair_5_6 a b

#print axioms cross_cone_lower5
#assert_trust kernel cross_cone_lower5

end NLA.PF03
