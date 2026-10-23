/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual row projections in the retained ordered-pivot/Hilbert graph interface.
-/
import NLA.Proofs.TR06.GraphProjectionLinear
import NLA.Proofs.TR06.GraphCharacterOrdered

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphProjection
open NLA.TR06 NLA.TR06.Segre GraphAlgebra GraphCharacter UnramifiedDifferential
variable {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
attribute [local instance] RingHom.ker_isPrime

/-- The exact row map on genuine original ordered-pivot normalized graph points. -/
def orderedRowValues (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) (p : OrderedPivotData q₀) : Fin k → ℝ :=
  fun j => ∑ c, rows j c *
    ambientValues (normalizedGraphPoint (pivotSum q₀ p) (orderedTensorFromPivotData q₀ p)) c

@[simp] theorem rowProjectedValues_pivotParameterEquiv (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) (p : OrderedPivotData q₀) :
    rowProjectedValues q₀ rows (pivotParameterEquiv q₀ p) = orderedRowValues q₀ rows p := by
  funext j
  simp only [rowProjectedValues,orderedRowValues,realGraphValues_ordered]

/-- The genuine projected derivative premise transfers through the exact
continuous linear parameter equivalence, without a metric claim. -/
theorem rowProjected_fderiv_injective_of_ordered
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ)
    (p : OrderedPivotData q₀) (hp : ∀ i, (p i).1 ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (orderedRowValues q₀ rows) p)) :
    Function.Injective (fderiv ℝ (rowProjectedValues q₀ rows) (pivotParameterEquiv q₀ p)) := by
  let e := pivotParameterEquiv q₀
  have hdiff := differentiableAt_rowProjectedValues q₀ rows (e p) (by simpa [e] using hp)
  have hcomp := hdiff.hasFDerivAt.comp p e.hasFDerivAt
  have hfun : (fun p : OrderedPivotData q₀ => rowProjectedValues q₀ rows (e p)) =
      orderedRowValues q₀ rows := by
    funext p
    exact rowProjectedValues_pivotParameterEquiv q₀ rows p
  change HasFDerivAt (fun p : OrderedPivotData q₀ => rowProjectedValues q₀ rows (e p))
    ((fderiv ℝ (rowProjectedValues q₀ rows) (e p)).comp e.toContinuousLinearMap) p at hcomp
  rw [hfun] at hcomp
  have hc : Function.Injective ((fderiv ℝ (rowProjectedValues q₀ rows) (e p)).comp e.toContinuousLinearMap) := by
    rw [← hcomp.fderiv]
    exact hinj
  intro x y hxy
  apply e.symm.injective
  apply hc
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hxy

/-- Actual quasi-finiteness for the original ordered-pivot normalized graph
projection, with the genuine derivative premise reserved for the geometric atlas. -/
theorem quasiFiniteAt_orderedRowProjection_of_fderiv_injective
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ)
    (p : OrderedPivotData q₀) (hp : ∀ i, (p i).1 ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (orderedRowValues q₀ rows) p)) :
    (rowProjectionHom q₀ rows).toRingHom.QuasiFiniteAt (RingHom.ker (orderedCharacter q₀ p hp).toRingHom) := by
  exact quasiFiniteAt_rowProjection_of_fderiv_injective q₀ rows (pivotParameterEquiv q₀ p)
    (by simpa using hp) (rowProjected_fderiv_injective_of_ordered q₀ rows p hp hinj)

#print axioms rowProjected_fderiv_injective_of_ordered
#print axioms quasiFiniteAt_orderedRowProjection_of_fderiv_injective
#assert_trust kernel rowProjected_fderiv_injective_of_ordered
#assert_trust kernel quasiFiniteAt_orderedRowProjection_of_fderiv_injective
end NLA.Proofs.TR06.GraphProjection
