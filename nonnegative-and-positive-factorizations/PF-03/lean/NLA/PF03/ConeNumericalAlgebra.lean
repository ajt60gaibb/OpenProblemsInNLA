import NLA.PF03.SeedLocalAlgebra
import NLA.PF03.QuadraticGeneratorCache

/-!
Exact cubic targets for the QG and cross-cone certificates.
No cached identity or sign is assumed by an exported conclusion.
Original mathematics and seed: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

def generatorIndex (i : Fin 7) (a : Fin 3) : Fin 21 :=
  (finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21) (i, a)

def quadraticGeneratorCubic (r : Fin 7) (j : Fin 21) : Cubic :=
  ∑ s : Fin 7, cubicScale (RawData.generators s j) (RawData.quadraticMatrix r s)

def crossCubic (i j : Fin 7) (a b : Fin 3) : Cubic :=
  ∑ r : Fin 7, cubicScale (RawData.generators r (generatorIndex i a))
    (ConeData.quadraticGeneratorCache r (generatorIndex j b))

theorem quadraticGeneratorCubic_eval (r : Fin 7) (j : Fin 21) :
    cubicEval (quadraticGeneratorCubic r j) =
      ∑ s : Fin 7, (RawData.generators s j : ℝ) *
        cubicEval (RawData.quadraticMatrix r s) := by
  simp only [quadraticGeneratorCubic, cubicEval_finset_sum, cubicEval_cubicScale]

#print axioms quadraticGeneratorCubic_eval
#assert_trust kernel quadraticGeneratorCubic_eval

end NLA.PF03
