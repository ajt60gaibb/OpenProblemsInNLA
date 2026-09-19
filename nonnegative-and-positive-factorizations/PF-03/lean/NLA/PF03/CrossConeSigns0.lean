import NLA.PF03.ConeNumericalAlgebra

/-! Exact rational lower bounds for ordered cross-cone pairs starting at 0. -/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace NLA.PF03

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem cross_cone_lower0 (j : Fin 7) (hij : (0 : Fin 7) < j) (a b : Fin 3) :
    0 < cubicLower (crossCubic 0 j a b) := by
  fin_cases j <;> norm_num at hij
  all_goals fin_cases a <;> fin_cases b <;> decide +kernel

#print axioms cross_cone_lower0
#assert_trust kernel cross_cone_lower0

end NLA.PF03
