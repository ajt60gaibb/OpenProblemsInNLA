import Mathlib
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06

/-- Finite coordinate-chart families combine uniform finite-subset fiber bounds.
The index assignment may depend on the actual point; no global chosen sheet
or uniqueness of its chart representation is required. -/
theorem finite_union_finite_subset_bound {ι α : Type*} [Fintype ι] [DecidableEq α]
    (S : Set α) (P : ι → α → Prop) (B : ι → ℕ)
    (hcover : ∀ z ∈ S, ∃ i, P i z)
    (hbound : ∀ i (q : Finset α), (↑q : Set α) ⊆ {z | z ∈ S ∧ P i z} → q.card ≤ B i)
    (q : Finset α) (hq : (↑q : Set α) ⊆ S) : q.card ≤ ∑ i, B i := by
  classical
  by_cases hι : Nonempty ι
  swap
  · have hqempty : q = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro z hz
      obtain ⟨i,_⟩ := hcover z (hq hz)
      exact hι ⟨i⟩)
    simp [hqempty]
  choose index hi using fun z : S => hcover z.val z.property
  let classify : α → ι := fun z => if hz : z ∈ S then index ⟨z,hz⟩ else Classical.choice hι
  have hsum : q.card = ∑ i, (q.filter (fun z => classify z = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hsum]
  apply Finset.sum_le_sum
  intro i _
  apply hbound i
  intro z hz
  obtain ⟨hzq,hzi⟩ := Finset.mem_filter.mp hz
  have hzS := hq hzq
  refine ⟨hzS,?_⟩
  have heq : classify z = index ⟨z,hzS⟩ := dif_pos hzS
  rw [heq] at hzi
  rw [← hzi]
  exact hi ⟨z,hzS⟩

#assert_trust kernel finite_union_finite_subset_bound
#print axioms finite_union_finite_subset_bound
end NLA.Proofs.TR06
