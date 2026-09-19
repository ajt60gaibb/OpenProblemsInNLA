import NLA.PF03.ConeNumericalAlgebra

/-! Exact coefficient identities for generator group 5; 21 cubic entries. -/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace NLA.PF03

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem quadratic_generator_block5 (b : Fin 3) (r : Fin 7) (k : Fin 3) :
    quadraticGeneratorCubic r (generatorIndex 5 b) k =
      ConeData.quadraticGeneratorCache r (generatorIndex 5 b) k := by
  fin_cases b <;> fin_cases r <;> fin_cases k <;> decide +kernel

#print axioms quadratic_generator_block5
#assert_trust kernel quadratic_generator_block5

end NLA.PF03
