/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06

variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ}

/-- The closed-cone candidate includes its zero vertex. Closedness is a
separate obligation; this definition makes no topological assertion. -/
def rankAtMostOne (A : Tensor 𝕜 d n) : Prop := A = 0 ∨ RankOne A

/-- Actual ordered tensor tuples, including any zero summands. -/
def closedRankOneProduct (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Set (Fin r → Tensor 𝕜 d n) := {a | ∀ i, rankAtMostOne (a i)}

/-- The entire addition fiber in the closed rank-one product. -/
def closedAdditionFiber (r : ℕ) (A : Tensor 𝕜 d n) : Set (Fin r → Tensor 𝕜 d n) :=
  {a | a ∈ closedRankOneProduct 𝕜 d n r ∧ ∑ i, a i = A}

/-- Remove every zero summand by enumerating exactly the nonzero positions.
If any term vanishes the new length is strictly smaller, including all empty
index and zero-sum cases covered by these quantifiers. -/
theorem exists_decomposes_remove_zeros {r : ℕ} (a : Fin r → Tensor 𝕜 d n)
    (ha : ∀ i, rankAtMostOne (a i)) :
    ∃ m : ℕ, m ≤ r ∧ ((∃ i, a i = 0) → m < r) ∧
      ∃ b : Fin m → Tensor 𝕜 d n, Decomposes b (∑ i, a i) := by
  classical
  let I := {i : Fin r // a i ≠ 0}
  let m := Fintype.card I
  let e : I ≃ Fin m := Fintype.equivFin I
  let b : Fin m → Tensor 𝕜 d n := fun j => a (e.symm j)
  have hle : m ≤ r := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin r => a i ≠ 0)
  have hlt : (∃ i, a i = 0) → m < r := by
    rintro ⟨i, hi⟩
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := fun i : Fin r => a i ≠ 0) (x := i) (not_ne_iff.mpr hi))
  refine ⟨m, hle, hlt, b, fun j => (ha (e.symm j)).resolve_left (e.symm j).property, ?_⟩
  have hzero : (∑ i : {i : Fin r // ¬a i ≠ 0}, a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact not_ne_iff.mp i.property
  have hsum : (∑ i : I, a i) = ∑ i : Fin r, a i := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : Fin r => a i ≠ 0) a
    rw [hzero, add_zero] at hsplit
    exact hsplit
  exact (Fintype.sum_equiv e.symm b (fun i : I => a i) (fun _ => rfl)).trans hsum

/-- Exact rank prevents a zero entry anywhere in the full closed-product fiber. -/
theorem rankOne_of_mem_closedAdditionFiber {r : ℕ} {A : Tensor 𝕜 d n}
    (hA : ExactRank r A) {a : Fin r → Tensor 𝕜 d n}
    (ha : a ∈ closedAdditionFiber r A) : ∀ i, RankOne (a i) := by
  intro i
  rcases ha.1 i with hzero | hnonzero
  · obtain ⟨m, _hle, hlt, b, hb⟩ := exists_decomposes_remove_zeros a ha.1
    have hm : m < r := hlt ⟨i, hzero⟩
    exact (hA.2 m hm ⟨b, ha.2 ▸ hb⟩).elim
  · exact hnonzero

/-- The closed-product fiber is finite and nonempty at every identifiable
exact-rank tensor. This concerns actual tensor tuples and includes r=0. -/
theorem closedAdditionFiber_finite_nonempty {r : ℕ} {A : Tensor 𝕜 d n}
    (hrank : ExactRank r A) (hident : Identifiable r A) :
    (closedAdditionFiber r A).Finite ∧ (closedAdditionFiber r A).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hrank.1
  constructor
  · apply (Set.finite_range (fun σ : Equiv.Perm (Fin r) => fun i => a (σ i))).subset
    intro b hb
    have hb' : Decomposes b A := ⟨rankOne_of_mem_closedAdditionFiber hrank hb, hb.2⟩
    obtain ⟨σ, hσ⟩ := hident a b ha hb'
    exact ⟨σ, funext (fun i => (hσ i).symm)⟩
  · exact ⟨a, (fun i => Or.inr (ha.1 i)), ha.2⟩

#print axioms exists_decomposes_remove_zeros
#print axioms rankOne_of_mem_closedAdditionFiber
#print axioms closedAdditionFiber_finite_nonempty
#assert_trust kernel exists_decomposes_remove_zeros
#assert_trust kernel rankOne_of_mem_closedAdditionFiber
#assert_trust kernel closedAdditionFiber_finite_nonempty
end NLA.TR06
