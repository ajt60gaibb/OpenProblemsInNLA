/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.AdditionOpen
import NLA.TR06.ImmersionPatch

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace NLA.TR06.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- A genuine injective Segre patch over a proper identifiable open has an open
partial homeomorphism into the whole identifiable set. -/
theorem exists_pivot_open_chart
    (U : Set (Tensor ℝ d n)) (hU : IsOpen U)
    (hgood : IdentifiableAdditionOn (r := r) U)
    (hproper : CompactAdditionPreimagesOn (r := r) U)
    (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (W : Set (OrderedPivotData q₀)) (hW : IsOpen W) (hne : W.Nonempty)
    (hWnz : ∀ p ∈ W, ∀ i, (p i).1 ≠ 0)
    (hWU : ∀ p ∈ W, pivotSum q₀ p ∈ U)
    (hinj : InjOn (pivotSum q₀) W) :
    ∃ e : OpenPartialHomeomorph (OrderedPivotData q₀) (identifiableRealSet d n r),
      e.source = W ∧ ∀ p ∈ W, (e p).val = pivotSum q₀ p := by
  classical
  let decoder : W → OrderedRankOne d n r := fun p =>
    ⟨orderedTensorFromPivotData q₀ p.val,
      fun i => tensorFromPivotData_rankOne (q₀ i) j₀ (p.val i) (hWnz p.val p.property i)⟩
  have hdecoder : Topology.IsOpenEmbedding decoder :=
    isOpenEmbedding_pivotDecoder q₀ j₀ W hW hWnz
  have hdecomp (p : W) : Decomposes (decoder p).val (pivotSum q₀ p.val) :=
    ⟨(decoder p).property, rfl⟩
  let f : W → identifiableRealSet d n r := fun p =>
    ⟨pivotSum q₀ p.val, hgood _ (hWU p.val p.property) ⟨(decoder p).val, hdecomp p⟩⟩
  have hfcont : Continuous f :=
    ((contDiff_pivotSum q₀ 1).continuous.comp continuous_subtype_val).subtype_mk _
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact hinj p.property q.property (congrArg Subtype.val hpq)
  have hfopen : IsOpenMap f := by
    intro s hs
    have hdecimage : IsOpen (decoder '' s) := hdecoder.isOpenMap s hs
    have hdecU : ∀ a ∈ decoder '' s, (∑ i, a.val i) ∈ U := by
      rintro a ⟨p, hp, rfl⟩
      exact hWU p.val p.property
    have hadd := isOpen_identifiable_addition_image U hU hproper (decoder '' s) hdecimage hdecU
    convert hadd using 1
    ext A
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨decoder p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨a, ⟨p, hp, rfl⟩, hsum⟩
      exact ⟨p, hp, Subtype.ext hsum⟩
  have hfemb : Topology.IsOpenEmbedding f :=
    (Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap).mpr ⟨hfcont, hfinj, hfopen⟩
  let : Nonempty W := hne.to_subtype
  let : Nonempty (identifiableRealSet d n r) := ⟨f (Classical.choice inferInstance)⟩
  let e₀ := hfemb.toOpenPartialHomeomorph f
  let e := e₀.lift_openEmbedding hW.isOpenEmbedding_subtypeVal
  refine ⟨e, ?_, ?_⟩
  · change Subtype.val '' (Set.univ : Set W) = W
    simp
  · intro p hp
    have heq := e₀.lift_openEmbedding_apply hW.isOpenEmbedding_subtypeVal (x := (⟨p, hp⟩ : W))
    exact congrArg Subtype.val heq

#print axioms exists_pivot_open_chart
#assert_trust kernel exists_pivot_open_chart
end NLA.TR06.Proposed
