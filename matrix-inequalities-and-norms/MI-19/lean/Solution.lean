/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's MI-19 counterexample.
-/
import NLA.MI19.Proof

set_option autoImplicit false
open scoped ComplexOrder

namespace NLA.MI19

theorem counterexample :
    gramFactor.conjTranspose * gramFactor = witness ∧
    witness.IsHermitian ∧ witness.PosSemidef ∧
    0 ≤ witnessQ ∧ witnessQ ≤ 1 ∧
    witnessSubset.Nonempty ∧ witnessSubset ≠ Finset.univ ∧
    (qPermanent witnessQ witness).im = 0 ∧
    (restrictedQPermanent witnessQ witness witnessSubset).im = 0 ∧
    qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset =
      (-3235575 / 16384 : ℂ) ∧
    qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset :=
  counterexample_proved

theorem not_subsetConjecture : ¬ SubsetConjecture :=
  not_subsetConjecture_proved

#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_subsetConjecture
#print axioms not_subsetConjecture

end NLA.MI19
