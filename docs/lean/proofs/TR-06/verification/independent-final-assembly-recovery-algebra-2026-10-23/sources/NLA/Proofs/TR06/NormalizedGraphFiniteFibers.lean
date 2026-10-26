import NLA.Proofs.TR06.NormalizedGraphQuasiFiniteControlled
import NLA.Proofs.TR06.GraphProjectionCharacterBound
import NLA.Proofs.TR06.GraphProjectionOrderedBound
import NLA.Proofs.TR06.FiniteUnionFiberBounds

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal
namespace NLA.Proofs.TR06
open Set NLA.TR06 NLA.TR06.Segre NLA.TR06.Area.Proposed
open GraphAlgebra GraphCharacter GraphProjection
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
attribute [local instance] RingHom.ker_isPrime

theorem normalizedPivotGraph_ambientValues (q : Fin r → TensorIndex d n)
    (p : Parameter ℝ q) : ambientValues (normalizedPivotGraph q p) = realGraphValues q p := by
  funext c
  cases c with
  | inl q => rfl
  | inr iq => rfl

/-- Every controlled projection fiber has a bound independent of its base
point. The finite pivot family covers all actual ordered graph branches. -/
theorem normalizedGraph_controlled_finite_subset_bound (hd : 0 < d)
    (K : ℝ≥0)
    (σ : Fin (expectedDimension d n r) ↪ Fin (graphAmbientDimension d n r)) :
    ∃ B : ℕ, ∀ x (q : Finset (Euclid (graphAmbientDimension d n r))),
      (↑q : Set _) ⊆ {z | z ∈ ControlledProjectionSet K (euclideanNormalizedGraph d n r) σ ∧
        coordProjection σ z = x} → q.card ≤ B := by
  classical
  let Q := Fin r → TensorIndex d n
  choose B hB using fun q₀ : Q => exists_uniform_row_character_family_bound q₀ (graphProjectionRows σ)
  refine ⟨∑ q₀, B q₀,?_⟩
  intro x q hq
  let S := {z | z ∈ ControlledProjectionSet K (euclideanNormalizedGraph d n r) σ ∧
    coordProjection σ z = x}
  let P : Q → Euclid (graphAmbientDimension d n r) → Prop := fun q₀ z =>
    ∃ (p : Parameter ℝ q₀) (hp : ∀ i, p ⟨i,none⟩ ≠ 0),
      graphEuclideanEquiv d n r (normalizedPivotGraph q₀ p) = z ∧
      (rowProjectionHom q₀ (graphProjectionRows σ)).toRingHom.QuasiFiniteAt
        (RingHom.ker (character q₀ p hp).toRingHom)
  have hcover : ∀ z ∈ S, ∃ q₀, P q₀ z := by
    intro z hz
    have hzgraph : z ∈ euclideanNormalizedGraph d n r := by
      obtain ⟨b,u,hu,hbu,_⟩ := hz.1
      rw [← hbu]
      exact (b u).property
    obtain ⟨w,hw,hew⟩ := hzgraph
    obtain ⟨q₀,p,hp,hpoint,_hderiv,hqf⟩ :=
      controlled_normalizedGraph_exists_quasiFinite_character hd σ ⟨w,hw⟩
        (by simpa only [hew] using hz.1)
    exact ⟨q₀,p,hp,(congrArg (graphEuclideanEquiv d n r) hpoint).trans hew,hqf⟩
  apply finite_union_finite_subset_bound S P B hcover ?_ q hq
  intro q₀ t ht
  choose p hp hpoint hqf using fun a : t => (ht a.property).2
  let χ : t → Source q₀ →ₐ[ℂ] ℂ := fun a => character q₀ (p a) (hp a)
  have hinj : Function.Injective χ := by
    intro a b hab
    apply Subtype.ext
    rw [← hpoint a,← hpoint b]
    congr 1
    apply ambientValues_injective
    funext c
    have H := congrArg (fun f : Source q₀ →ₐ[ℂ] ℂ => f (graphCoordinate q₀ c)) hab
    change character q₀ (p a) (hp a) (graphCoordinate q₀ c) =
      character q₀ (p b) (hp b) (graphCoordinate q₀ c) at H
    rw [character_graphCoordinate,character_graphCoordinate] at H
    rw [normalizedPivotGraph_ambientValues,normalizedPivotGraph_ambientValues]
    exact Complex.ofReal_injective H
  have hval : ∀ a j, χ a (rowProjectionCoordinate q₀ (graphProjectionRows σ) j) = (x j : ℂ) := by
    intro a j
    change character q₀ (p a) (hp a) (rowProjectionCoordinate q₀ (graphProjectionRows σ) j) = _
    rw [character_rowProjectionCoordinate,normalizedPivotGraph_rows,hpoint a,(ht a.property).1.2]
  have H := hB q₀ x.ofLp t χ hinj hval hqf
  simpa only [Fintype.card_coe] using H

#assert_trust kernel normalizedPivotGraph_ambientValues
#assert_trust kernel normalizedGraph_controlled_finite_subset_bound
#print axioms normalizedGraph_controlled_finite_subset_bound
end NLA.Proofs.TR06
