import NLA.PF03.ConeNumericalAlgebra

/-!
C10 internal signs for lower group 3. Only literal upper groups enter the
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
private theorem cross_cone_lower_pair_3_4 (a b : Fin 3) :
    0 < cubicLower (crossCubic 3 4 a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cross_cone_lower_pair_3_5 (a b : Fin 3) :
    0 < cubicLower (crossCubic 3 5 a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cross_cone_lower_pair_3_6 (a b : Fin 3) :
    0 < cubicLower (crossCubic 3 6 a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem cross_cone_lower3 (j : Fin 7) (hij : (3 : Fin 7) < j) (a b : Fin 3) :
    0 < cubicLower (crossCubic 3 j a b) := by
  change 3 < j.val at hij
  have hjbound : j.val < 7 := j.isLt
  have hjcases : j.val = 4 ∨ j.val = 5 ∨ j.val = 6 := by omega
  rcases hjcases with h4 | h5 | h6
  · have hj : j = (4 : Fin 7) := Fin.ext h4
    subst j
    exact cross_cone_lower_pair_3_4 a b
  · have hj : j = (5 : Fin 7) := Fin.ext h5
    subst j
    exact cross_cone_lower_pair_3_5 a b
  · have hj : j = (6 : Fin 7) := Fin.ext h6
    subst j
    exact cross_cone_lower_pair_3_6 a b

#print axioms cross_cone_lower3
#assert_trust kernel cross_cone_lower3

end NLA.PF03
