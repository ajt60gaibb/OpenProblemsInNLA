/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.AdditionNoEscape

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace NLA.TR06.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def permuteRankOne (σ : Equiv.Perm (Fin r)) (a : OrderedRankOne d n r) :
    OrderedRankOne d n r := ⟨fun i => a.val (σ i), fun i => a.property (σ i)⟩

lemma continuous_permuteRankOne (σ : Equiv.Perm (Fin r)) :
    Continuous (permuteRankOne (d := d) (n := n) σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (σ i)).comp continuous_subtype_val

lemma sum_permuteRankOne (σ : Equiv.Perm (Fin r)) (a : OrderedRankOne d n r) :
    (∑ i, (permuteRankOne σ a).val i) = ∑ i, a.val i := by
  exact Equiv.sum_comp σ a.val

/-- On an ambient properness open, the image of every open ordered-decomposition
set is open relative to the entire actual identifiable locus. -/
theorem isOpen_identifiable_addition_image
    (U : Set (Tensor ℝ d n)) (hU : IsOpen U)
    (hproper : CompactAdditionPreimagesOn (r := r) U)
    (V : Set (OrderedRankOne d n r)) (hV : IsOpen V)
    (hVU : ∀ a ∈ V, (∑ i, a.val i) ∈ U) :
    IsOpen {A : identifiableRealSet d n r |
      ∃ a ∈ V, (∑ i, a.val i) = A.val} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro A ⟨a, haV, haA⟩
  let W : Set (OrderedRankOne d n r) :=
    {b | ∃ σ : Equiv.Perm (Fin r), permuteRankOne σ b ∈ V}
  have hW : IsOpen W := by
    dsimp only [W]
    rw [Set.ofPred_exists]
    exact isOpen_iUnion (fun σ => hV.preimage (continuous_permuteRankOne σ))
  have hfiber : ∀ b : OrderedRankOne d n r, (∑ i, b.val i) = A.val → b ∈ W := by
    intro b hbA
    obtain ⟨σ, hσ⟩ := A.property.2 a.val b.val ⟨a.property, haA⟩ ⟨b.property, hbA⟩
    refine ⟨σ.symm, ?_⟩
    have heq : permuteRankOne σ.symm b = a := by
      apply Subtype.ext
      funext i
      simpa only [permuteRankOne, Equiv.apply_symm_apply] using hσ (σ.symm i)
    rw [heq]
    exact haV
  have hAU : A.val ∈ U := haA ▸ hVU a haV
  obtain ⟨ε, hε, hnear⟩ := addition_fiber_neighborhood d n r U hU hproper
    A.val hAU A.property.1 W hW hfiber
  have hnhds : {B : identifiableRealSet d n r | dist B.val A.val < ε} ∈ 𝓝 A :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds A.val hε)
  filter_upwards [hnhds] with B hB
  obtain ⟨b, hb⟩ := B.property.1.1
  let b' : OrderedRankOne d n r := ⟨b, hb.1⟩
  have hclose : dist (∑ i, b'.val i) A.val < ε := by
    change dist (∑ i, b i) A.val < ε
    rw [hb.2]
    exact hB
  obtain ⟨σ, hσ⟩ := hnear b' hclose
  exact ⟨permuteRankOne σ b', hσ, (sum_permuteRankOne σ b').trans hb.2⟩

/-- Restriction of the genuine pivot decoder to any open nonzero-amplitude
parameter set is an open embedding into the whole ordered rank-one product. -/
theorem isOpenEmbedding_pivotDecoder
    (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (W : Set (OrderedPivotData q₀)) (hW : IsOpen W)
    (hWnz : ∀ p ∈ W, ∀ i, (p i).1 ≠ 0) :
    Topology.IsOpenEmbedding (fun p : W =>
      (⟨orderedTensorFromPivotData q₀ p.val,
        fun i => tensorFromPivotData_rankOne (q₀ i) j₀ (p.val i) (hWnz p.val p.property i)⟩ :
        OrderedRankOne d n r)) := by
  let V : Set (OrderedPivotData q₀) := {p | ∀ i, (p i).1 ≠ 0}
  have hsub : W ⊆ V := hWnz
  have hinc : Topology.IsOpenEmbedding (Set.inclusion hsub) :=
    Topology.IsOpenEmbedding.inclusion hsub (hW.preimage continuous_subtype_val)
  let H := orderedRankOnePivotHomeomorph q₀ j₀
  have hdec : Topology.IsOpenEmbedding (fun p : V => (H.symm p).val) :=
    (isOpen_orderedRankOnePivotSet q₀).isOpenEmbedding_subtypeVal.comp H.symm.isOpenEmbedding
  exact hdec.comp hinc

#print axioms isOpen_identifiable_addition_image
#print axioms isOpenEmbedding_pivotDecoder
#assert_trust kernel isOpen_identifiable_addition_image
#assert_trust kernel isOpenEmbedding_pivotDecoder
end NLA.TR06.Proposed
