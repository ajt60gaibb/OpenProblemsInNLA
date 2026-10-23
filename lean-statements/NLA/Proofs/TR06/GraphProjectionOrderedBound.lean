/-
Copyright (c) 2026. Released under Apache 2.0 license.
Uniform bounds for finite families of actual ordered-pivot normalized graph points.
-/
import NLA.Proofs.TR06.GraphProjectionCharacterBound
import NLA.Proofs.TR06.GraphProjectionOrdered

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.GraphProjection
open NLA.TR06 NLA.TR06.Segre GraphAlgebra GraphCharacter
variable {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}

/-- Literal input and output coordinates separate the genuine Hilbert graph ambient. -/
theorem ambientValues_injective :
    Function.Injective (@ambientValues d n r) := by
  intro z w h
  apply (WithLp.ext_iff 2).2
  apply Prod.ext
  · apply (WithLp.ext_iff 2).2
    funext q
    exact congrFun h (Sum.inl q)
  · apply (WithLp.ext_iff 2).2
    funext iq
    exact congrFun h (Sum.inr iq)

/-- One bound works for all finite families of distinct actual graph points in
one fixed pivot pattern and one fixed row-projection fiber. Genuine derivative
injectivity is the local hypothesis supplied by the separate geometric atlas. -/
theorem exists_uniform_ordered_graph_family_bound
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ) :
    ∃ B : ℕ, ∀ (x : Fin k → ℝ) (ι : Type*) [Fintype ι]
      (p : ι → OrderedPivotData q₀) (hp : ∀ a i, (p a i).1 ≠ 0),
      Function.Injective (fun a =>
        normalizedGraphPoint (pivotSum q₀ (p a)) (orderedTensorFromPivotData q₀ (p a))) →
      (∀ a, orderedRowValues q₀ rows (p a) = x) →
      (∀ a, Function.Injective (fderiv ℝ (orderedRowValues q₀ rows) (p a))) →
      Fintype.card ι ≤ B := by
  obtain ⟨B,hB⟩ := exists_uniform_row_character_family_bound q₀ rows
  refine ⟨B,?_⟩
  intro x ι _ p hp hpoints hval hderiv
  let χ : ι → Source q₀ →ₐ[ℂ] ℂ := fun a => orderedCharacter q₀ (p a) (hp a)
  have hinj : Function.Injective χ := by
    intro a b hab
    apply hpoints
    apply ambientValues_injective
    funext c
    have hc := congrArg (fun f : Source q₀ →ₐ[ℂ] ℂ => f (graphCoordinate q₀ c)) hab
    change orderedCharacter q₀ (p a) (hp a) (graphCoordinate q₀ c) =
      orderedCharacter q₀ (p b) (hp b) (graphCoordinate q₀ c) at hc
    rw [orderedCharacter_graphCoordinate,orderedCharacter_graphCoordinate] at hc
    exact Complex.ofReal_injective hc
  apply hB x ι χ hinj
  · intro a j
    have H := character_rowProjectionCoordinate q₀ rows
      (UnramifiedDifferential.pivotParameterEquiv q₀ (p a)) (by simpa using hp a) j
    simpa only [χ,orderedCharacter,rowProjectedValues_pivotParameterEquiv,hval a] using H
  · intro a
    exact quasiFiniteAt_orderedRowProjection_of_fderiv_injective q₀ rows (p a) (hp a) (hderiv a)

#print axioms ambientValues_injective
#print axioms exists_uniform_ordered_graph_family_bound
#assert_trust kernel ambientValues_injective
#assert_trust kernel exists_uniform_ordered_graph_family_bound
end NLA.Proofs.TR06.GraphProjection
