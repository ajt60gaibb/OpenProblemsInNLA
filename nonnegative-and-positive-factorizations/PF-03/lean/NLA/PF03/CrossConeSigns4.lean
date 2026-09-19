import NLA.PF03.ConeNumericalAlgebra

/-!
C10 internal signs for lower group 4. Only literal upper groups enter the
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
private theorem cross_cone_lower_pair_4_5 (a b : Fin 3) :
    0 < cubicLower (crossCubic 4 5 a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cross_cone_lower_pair_4_6 (a b : Fin 3) :
    0 < cubicLower (crossCubic 4 6 a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem cross_cone_lower4 (j : Fin 7) (hij : (4 : Fin 7) < j) (a b : Fin 3) :
    0 < cubicLower (crossCubic 4 j a b) := by
  change 4 < j.val at hij
  have hjbound : j.val < 7 := j.isLt
  have hjcases : j.val = 5 ∨ j.val = 6 := by omega
  rcases hjcases with h5 | h6
  · have hj : j = (5 : Fin 7) := Fin.ext h5
    subst j
    exact cross_cone_lower_pair_4_5 a b
  · have hj : j = (6 : Fin 7) := Fin.ext h6
    subst j
    exact cross_cone_lower_pair_4_6 a b

#print axioms cross_cone_lower4
#assert_trust kernel cross_cone_lower4

end NLA.PF03
