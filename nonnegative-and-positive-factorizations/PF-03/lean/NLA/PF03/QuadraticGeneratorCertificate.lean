import NLA.PF03.QuadraticGeneratorBlock0
import NLA.PF03.QuadraticGeneratorBlock1
import NLA.PF03.QuadraticGeneratorBlock2
import NLA.PF03.QuadraticGeneratorBlock3
import NLA.PF03.QuadraticGeneratorBlock4
import NLA.PF03.QuadraticGeneratorBlock5
import NLA.PF03.QuadraticGeneratorBlock6

/-! All 147 proposed QG cubic entries now linked to the actual finite sums. -/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace NLA.PF03

theorem quadraticGeneratorCubic_cache (r : Fin 7) (j : Fin 21) :
    quadraticGeneratorCubic r j = ConeData.quadraticGeneratorCache r j := by
  rcases (finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).surjective j with ⟨⟨i, b⟩, rfl⟩
  change quadraticGeneratorCubic r (generatorIndex i b) =
    ConeData.quadraticGeneratorCache r (generatorIndex i b)
  funext k
  fin_cases i
  · exact quadratic_generator_block0 b r k
  · exact quadratic_generator_block1 b r k
  · exact quadratic_generator_block2 b r k
  · exact quadratic_generator_block3 b r k
  · exact quadratic_generator_block4 b r k
  · exact quadratic_generator_block5 b r k
  · exact quadratic_generator_block6 b r k

#print axioms quadraticGeneratorCubic_cache
#assert_trust kernel quadraticGeneratorCubic_cache

end NLA.PF03
