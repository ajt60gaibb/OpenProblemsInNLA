import NLA.Proofs.SP14.BaseExteriorFactor
import NLA.Proofs.SP14.EndpointNegativeTruncation
import NLA.Proofs.SP14.EndpointBaseSeries

/-!
The exact base endpoint square/zero and weighted finite-truncation density.
These are the first three conclusions in the independently reviewed
endpoint-vanishing contract. The pointwise operator bound is separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The already normalized endpoint series is the same square-root factor
used in the canonical exterior calculation. -/
theorem endpointBaseSymbol_sq (z : Circle) :
    endpointBaseSymbol z ^ 2 = 1 + (z : ℂ)⁻¹ := by
  simpa only [endpointBaseSymbol, baseExteriorFactor] using
    baseExteriorFactor_sq z

/-- The actual normalized endpoint series vanishes at the circle point -1. -/
theorem endpointBaseSymbol_neg_one :
    endpointBaseSymbol (-1 : Circle) = 0 := by
  simpa only [endpointBaseSymbol, baseExteriorFactor] using
    baseExteriorFactor_at_neg_one

/-- Literal finite coordinate truncations tend to every weighted ℓ² input. -/
theorem sobolevTruncation_tendsto (r : ℝ) (y : SobolevCoeff r) :
    Filter.Tendsto (fun N : ℕ => sobolevTruncation r N y)
      Filter.atTop (nhds y) :=
  tendsto_sobolevTruncation r y

#assert_trust kernel endpointBaseSymbol_sq
#assert_trust kernel endpointBaseSymbol_neg_one
#assert_trust kernel sobolevTruncation_tendsto
#print axioms sobolevTruncation_tendsto

end NLA.Proofs.SP14
