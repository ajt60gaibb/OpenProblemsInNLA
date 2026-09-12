/- Target environment for independent statement review and Comparator.
The deliberate placeholders below are never imported by the solution. -/
import NLA.MI19.Definitions

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
    qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset := by
  sorry

theorem not_subsetConjecture : ¬ SubsetConjecture := by
  sorry

end NLA.MI19
