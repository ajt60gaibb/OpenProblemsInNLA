/- The independently reviewed statement template. Intentional theorem holes
are excluded from proof-development sorry counts and never imported by Solution. -/
import NLA.MI21.Definitions

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section

namespace NLA.MI21

/-- The selected concrete norm satisfies every norm and invariance axiom in
the original universal target, in every matrix dimension. -/
theorem operatorNorm_isUnitaryInvariant (n : ℕ) :
    IsUnitaryInvariantNorm (operatorNorm (n := n)) := by
  sorry

/-- The exact complex positive definite inputs and actual CFC expressions
give a strict operator-norm violation for every positive outer parameter. -/
theorem counterexample (p : ℝ) (hp : 0 < p) :
    (∀ i : Fin 2, (witnessA i).PosDef ∧ (witnessB i).PosDef) ∧
    (∑ i, witnessA i) = 1 ∧ (∑ i, witnessB i) = 1 ∧
    leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2 = witnessL ∧
    rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p = 1 ∧
    witnessVector ≠ 0 ∧
    witnessL *ᵥ witnessVector = (witnessEigenvalue : ℂ) • witnessVector ∧
    1 < witnessEigenvalue ∧
    witnessEigenvalue ≤ operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) ∧
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) = 1 ∧
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) <
      operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) := by
  sorry

/-- A full negative answer to the exact canonical universally quantified target. -/
theorem not_geometricMeanNormConjecture : ¬ GeometricMeanNormConjecture := by
  sorry

end NLA.MI21
