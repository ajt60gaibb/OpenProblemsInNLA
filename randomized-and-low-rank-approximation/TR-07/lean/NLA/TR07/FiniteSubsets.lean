import NLA.TR07.FiniteSampling
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace NLA.TR07
open Law

abbrev SubsetSample (α : Type*) [Fintype α] (r : ℕ) :=
  ↥((Finset.univ : Finset α).powersetCard r)

def orderedRange {α : Type*} [Fintype α] {r : ℕ} (e : Fin r ↪ α) : Finset α :=
  Finset.univ.map e

@[simp] theorem orderedRange_card {α : Type*} [Fintype α] {r : ℕ} (e : Fin r ↪ α) :
    (orderedRange e).card = r := by simp [orderedRange]

def orderedRangeSample {α : Type*} [Fintype α] {r : ℕ} (e : Fin r ↪ α) : SubsetSample α r :=
  ⟨orderedRange e, by simp [Finset.mem_powersetCard]⟩

theorem subsetSample_card {α : Type*} [Fintype α] {r : ℕ} (S : SubsetSample α r) :
    S.val.card = r := (Finset.mem_powersetCard.mp S.property).2

def equivEmbedding {α : Type*} [Fintype α] {r : ℕ} (S : SubsetSample α r)
    (e : Fin r ≃ S.val) : Fin r ↪ α :=
  e.toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem equivEmbedding_apply {α : Type*} [Fintype α] {r : ℕ}
    (S : SubsetSample α r) (e : Fin r ≃ S.val) (i : Fin r) :
    equivEmbedding S e i = (e i).val := rfl

@[simp] theorem orderedRange_equivEmbedding {α : Type*} [Fintype α] {r : ℕ}
    (S : SubsetSample α r) (e : Fin r ≃ S.val) : orderedRange (equivEmbedding S e) = S.val := by
  ext a
  simp only [orderedRange, Finset.mem_map, Finset.mem_univ, true_and, equivEmbedding_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro ha
    exact ⟨e.symm ⟨a,ha⟩, by simp⟩

def rangeFiberEquiv {α : Type*} [Fintype α] {r : ℕ} (S : SubsetSample α r) :
    {e : Fin r ↪ α // orderedRangeSample e = S} ≃ (Fin r ≃ S.val) where
  toFun e := Equiv.ofBijective (fun i => ⟨e.val i, by
    have h : orderedRange e.val = S.val := congrArg Subtype.val e.property
    rw [← h]
    simp [orderedRange]⟩) ⟨by
      intro i j hij
      exact e.val.injective (congrArg Subtype.val hij), by
      intro a
      have h : a.val ∈ orderedRange e.val := by
        rw [show orderedRange e.val = S.val from congrArg Subtype.val e.property]
        exact a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨equivEmbedding S e, Subtype.ext (orderedRange_equivEmbedding S e)⟩
  left_inv e := by apply Subtype.ext; ext i; rfl
  right_inv e := by ext i; rfl

@[simp] theorem card_range_fiber {α : Type*} [Fintype α] {r : ℕ} (S : SubsetSample α r) :
    Fintype.card {e : Fin r ↪ α // orderedRangeSample e = S} = r.factorial := by
  rw [Fintype.card_congr (rangeFiberEquiv S)]
  simpa using Fintype.card_equiv (Finset.equivFinOfCardEq (subsetSample_card S)).symm

/-- Averaging an observable of the unordered range over all orderings does not change its law. -/
theorem ordered_range_expect {α : Type*} [Fintype α] {r : ℕ}
    (hr : r ≤ Fintype.card α) (f : Finset α → ℝ) :
    (orderedLaw α r hr).expect (fun e => f (orderedRange e)) =
      (∑ S ∈ (Finset.univ : Finset α).powersetCard r, f S) /
        ((Finset.univ : Finset α).powersetCard r).card := by
  have hcard : Fintype.card (Fin r ↪ α) =
      Fintype.card (SubsetSample α r) * r.factorial := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (@orderedRangeSample α _ r))]
    simp [Fintype.card_sigma]
  have hsum : (∑ e : Fin r ↪ α, f (orderedRange e)) =
      (r.factorial : ℝ) * ∑ S : SubsetSample α r, f S.val := by
    rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv (@orderedRangeSample α _ r)), Fintype.sum_sigma]
    change (∑ S : SubsetSample α r, ∑ e : {e : Fin r ↪ α // orderedRangeSample e = S},
      f (orderedRange e.val)) = _
    have he (S : SubsetSample α r) :
        (∑ e : {e : Fin r ↪ α // orderedRangeSample e = S}, f (orderedRange e.val)) =
          (r.factorial:ℝ) * f S.val := by
      have hf (e : {e : Fin r ↪ α // orderedRangeSample e = S}) :
          f (orderedRange e.val) = f S.val := congrArg f (congrArg Subtype.val e.property)
      simp_rw [hf]
      simp
    simp_rw [he]
    rw [Finset.mul_sum]
  rw [orderedLaw_expect, hsum, hcard]
  simp only [Nat.cast_mul, Fintype.card_coe]
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero r)
  rw [mul_comm _ (r.factorial:ℝ), mul_div_mul_left _ _ hf]
  congr 1
  exact Finset.sum_coe_sort _ _

def subsetProbability (n r : ℕ) (P : Finset (Fin n) → Prop) : ℝ :=
  (((Finset.univ : Finset (Fin n)).powersetCard r).filter P).card /
    (((Finset.univ : Finset (Fin n)).powersetCard r).card : ℝ)

theorem ordered_range_prob {n r : ℕ} (hr : r ≤ n) (P : Finset (Fin n) → Prop) :
    (orderedLaw (Fin n) r (by simpa)).prob (fun e => P (orderedRange e)) =
      subsetProbability n r P := by
  rw [Law.prob, ordered_range_expect (by simpa using hr) (fun S => if P S then 1 else 0)]
  unfold subsetProbability
  rw [Finset.sum_boole]

end NLA.TR07
