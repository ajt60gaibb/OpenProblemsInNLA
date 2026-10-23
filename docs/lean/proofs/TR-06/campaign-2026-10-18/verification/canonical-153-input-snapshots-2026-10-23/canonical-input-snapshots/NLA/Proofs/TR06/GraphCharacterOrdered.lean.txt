/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual graph characters in retained ordered-pivot and Hilbert graph coordinates.
-/
import NLA.Proofs.TR06.GraphCharacterReal
import NLA.Proofs.TR06.UnramifiedDifferentialReal
import NLA.Proofs.TR06.NormalizedGraphDefinitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.GraphCharacter
open NLA.TR06 NLA.TR06.Segre GraphAlgebra UnramifiedDifferential
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Literal input/output coordinates of the genuine Hilbert graph ambient. -/
def ambientValues (w : NormalizedGraphAmbient d n r) : OutputCoordinate d n r → ℝ
  | Sum.inl q => w.ofLp.1 q
  | Sum.inr iq => w.ofLp.2 iq

/-- The actual character in the original ordered-pivot data interface. -/
def orderedCharacter (q₀ : Fin r → TensorIndex d n) (p : OrderedPivotData q₀)
    (hp : ∀ i, (p i).1 ≠ 0) : Source q₀ →ₐ[ℂ] ℂ :=
  character q₀ (pivotParameterEquiv q₀ p) hp

/-- No coordinate, norm, ordering or branch change is hidden in the passage
from the algebraic character to the actual Hilbert graph point. -/
theorem realGraphValues_ordered (q₀ : Fin r → TensorIndex d n) (p : OrderedPivotData q₀) :
    realGraphValues q₀ (pivotParameterEquiv q₀ p) =
      ambientValues (normalizedGraphPoint (pivotSum q₀ p) (orderedTensorFromPivotData q₀ p)) := by
  funext c
  cases c with
  | inl q => simp only [realGraphValues,sum_pivotParameterEquiv,ambientValues,normalizedGraphPoint]
  | inr iq =>
    rcases iq with ⟨i,q⟩
    simp only [realGraphValues,summands_pivotParameterEquiv,ambientValues,normalizedGraphPoint,
      normalizedTuple,orderedTensorFromPivotData]

/-- Actual character evaluation agrees with the genuine normalized graph. -/
theorem orderedCharacter_graphCoordinate (q₀ : Fin r → TensorIndex d n) (p : OrderedPivotData q₀)
    (hp : ∀ i, (p i).1 ≠ 0) (c : OutputCoordinate d n r) :
    orderedCharacter q₀ p hp (graphCoordinate q₀ c) =
      (ambientValues (normalizedGraphPoint (pivotSum q₀ p) (orderedTensorFromPivotData q₀ p)) c : ℂ) := by
  change character q₀ (pivotParameterEquiv q₀ p) hp (graphCoordinate q₀ c) = _
  rw [character_graphCoordinate,realGraphValues_ordered]

#print axioms realGraphValues_ordered
#print axioms orderedCharacter_graphCoordinate
#assert_trust kernel realGraphValues_ordered
#assert_trust kernel orderedCharacter_graphCoordinate
end NLA.Proofs.TR06.GraphCharacter
