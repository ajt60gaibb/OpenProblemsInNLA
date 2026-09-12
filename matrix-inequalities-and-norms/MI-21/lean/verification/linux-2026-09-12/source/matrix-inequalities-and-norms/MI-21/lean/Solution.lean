/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-21.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI21.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section

namespace NLA.MI21

/-- The selected concrete norm satisfies every norm and invariance axiom in
the original universal target, in every matrix dimension. -/
theorem operatorNorm_isUnitaryInvariant (n : ℕ) :
    IsUnitaryInvariantNorm (operatorNorm (n := n)) := by
  exact operatorNorm_isUnitaryInvariant_proved n

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
  exact counterexample_proved p hp

/-- A full negative answer to the exact canonical universally quantified target. -/
theorem not_geometricMeanNormConjecture : ¬ GeometricMeanNormConjecture := by
  exact not_geometricMeanNormConjecture_proved

#assert_trust kernel operatorNorm_isUnitaryInvariant
#assert_trust kernel counterexample
#assert_trust kernel not_geometricMeanNormConjecture

#print axioms operatorNorm_isUnitaryInvariant
#print axioms counterexample
#print axioms not_geometricMeanNormConjecture

end NLA.MI21
