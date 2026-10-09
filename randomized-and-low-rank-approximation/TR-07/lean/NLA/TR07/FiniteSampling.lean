import NLA.TR07.FiniteVariance
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace NLA.TR07
open Law

namespace Law
variable {α : Type*} [Fintype α] [Nonempty α]

/-- Resample uniformly in a nonempty subset only when the original draw misses it. -/
def repair (S : Finset α) (hS : S.Nonempty) : Law (α × S) := by
  classical
  letI : Nonempty S := hS.to_subtype
  exact (uniform α).bind (fun a =>
    if ha : a ∈ S then pure (a, ⟨a, ha⟩)
    else (uniform S).map (fun b => (a, b)))

theorem expect_repair_fst (S : Finset α) (hS : S.Nonempty) (f : α → ℝ) :
    (repair S hS).expect (fun x => f x.1) = (uniform α).expect f := by
  classical
  unfold repair
  rw [expect_bind]
  apply expect_congr
  intro a
  split_ifs <;> simp

theorem expect_repair_snd (S : Finset α) (hS : S.Nonempty) (f : S → ℝ) :
    (repair S hS).expect (fun x => f x.2) =
      @Law.expect S _ (@uniform S _ hS.to_subtype) f := by
  classical
  let : Nonempty S := hS.to_subtype
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold repair
  rw [expect_bind, uniform_expect]
  have he (a : α) :
      (if ha : a ∈ S then pure (a, ⟨a,ha⟩) else (uniform S).map (fun b => (a,b))).expect
        (fun x => f x.2) = if ha : a ∈ S then f ⟨a,ha⟩ else (uniform S).expect f := by
    split_ifs <;> simp
  simp_rw [he]
  have hsum : (∑ a : α, if ha : a ∈ S then f ⟨a,ha⟩ else (uniform S).expect f) =
      (∑ a : S, f a) + ((Fintype.card α - S.card : ℕ) : ℝ) * (uniform S).expect f := by
    rw [Finset.sum_dite]
    congr 1
    · exact Equiv.sum_comp (Equiv.subtypeEquivRight (fun a : α =>
        show a ∈ Finset.univ.filter (fun x => x ∈ S) ↔ a ∈ S by simp)) f
    · simp [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  rw [hsum, uniform_expect]
  simp only [Fintype.card_coe]
  rw [Nat.cast_sub (Finset.card_le_univ S)]
  field_simp
  ring

theorem expect_repair_mismatch (S : Finset α) (hS : S.Nonempty) :
    (repair S hS).expect (fun x => if x.1 ≠ x.2.1 then 1 else 0) =
      ((Fintype.card α - S.card : ℕ) : ℝ) / Fintype.card α := by
  classical
  let : Nonempty S := hS.to_subtype
  unfold repair
  rw [expect_bind, uniform_expect]
  have h (a : α) :
      (if ha : a ∈ S then pure (a, ⟨a,ha⟩) else (uniform S).map (fun b => (a,b))).expect
        (fun x => if x.1 ≠ x.2.1 then (1:ℝ) else 0) = if a ∉ S then 1 else 0 := by
    split_ifs with ha
    · simp
    · rw [expect_map]
      have he : (fun b : S => if a ≠ b.val then (1:ℝ) else 0) = fun _ => 1 := by
        funext b
        simp only [ne_eq, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
        intro hab
        exact ha (hab ▸ b.property)
      simp only [he, expect_const]
  simp_rw [h]
  congr 1
  rw [Finset.sum_boole]
  simp [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ S)]

end Law

/-- Uniform ordered samples with distinct entries. -/
def orderedLaw (α : Type*) [Fintype α] (r : ℕ) (hr : r ≤ Fintype.card α) :
    Law (Fin r ↪ α) := by
  letI : Nonempty (Fin r ↪ α) := Function.Embedding.nonempty_of_card_le (by simpa)
  exact Law.uniform _

@[simp] theorem orderedLaw_expect {α : Type*} [Fintype α] (r : ℕ) (hr : r ≤ Fintype.card α)
    (f : (Fin r ↪ α) → ℝ) :
    (orderedLaw α r hr).expect f = (∑ e, f e) / Fintype.card (Fin r ↪ α) := by
  let : Nonempty (Fin r ↪ α) := Function.Embedding.nonempty_of_card_le (by simpa)
  exact uniform_expect f

def freshSet {α : Type*} [Fintype α] {r : ℕ} (e : Fin r ↪ α) : Finset α := by
  classical
  exact Finset.univ \ Finset.univ.map e

@[simp] theorem mem_freshSet {α : Type*} [Fintype α] {r : ℕ} (e : Fin r ↪ α) (a : α) :
    a ∈ freshSet e ↔ a ∉ Set.range e := by
  classical
  simp [freshSet, Set.mem_range]

@[simp] theorem freshSet_card {α : Type*} [Fintype α] {r : ℕ} (e : Fin r ↪ α) :
    (freshSet e).card = Fintype.card α - r := by
  classical
  simp [freshSet, Finset.card_sdiff_of_subset (Finset.subset_univ _)]

theorem freshSet_nonempty {α : Type*} [Fintype α] {r : ℕ}
    (e : Fin r ↪ α) (hr : r < Fintype.card α) : (freshSet e).Nonempty := by
  rw [← Finset.card_pos, freshSet_card]
  omega

def consEmbedding {α : Type*} [Fintype α] {r : ℕ}
    (e : Fin r ↪ α) (a : freshSet e) : Fin (r+1) ↪ α :=
  (Equiv.embeddingFinSucc r α).symm ⟨e, a.val, (mem_freshSet e a.val).mp a.property⟩

@[simp] theorem coe_consEmbedding {α : Type*} [Fintype α] {r : ℕ}
    (e : Fin r ↪ α) (a : freshSet e) :
    (consEmbedding e a : Fin (r+1) → α) = Fin.cons a.val e := by
  exact Equiv.coe_embeddingFinSucc_symm _

def orderedConsEquiv (α : Type*) [Fintype α] (r : ℕ) :
    (Σ e : Fin r ↪ α, freshSet e) ≃ (Fin (r+1) ↪ α) :=
  (Equiv.sigmaCongrRight (fun e => Equiv.subtypeEquivRight (mem_freshSet e))).trans
    (Equiv.embeddingFinSucc r α).symm

@[simp] theorem orderedConsEquiv_apply {α : Type*} [Fintype α] {r : ℕ}
    (e : Fin r ↪ α) (a : freshSet e) :
    orderedConsEquiv α r ⟨e,a⟩ = consEmbedding e a := rfl

theorem orderedLaw_cons_expect {α : Type*} [Fintype α] {r : ℕ}
    (hr : r+1 ≤ Fintype.card α) (f : (Fin (r+1) ↪ α) → ℝ) :
    (orderedLaw α (r+1) hr).expect f =
      (orderedLaw α r (by omega)).expect (fun e =>
        @Law.expect (freshSet e) _
          (@Law.uniform (freshSet e) _ (freshSet_nonempty e (by omega)).to_subtype)
          (fun a => f (consEmbedding e a))) := by
  simp only [orderedLaw_expect, uniform_expect, Fintype.card_coe, freshSet_card]
  rw [← Equiv.sum_comp (orderedConsEquiv α r), Fintype.sum_sigma]
  simp only [orderedConsEquiv_apply]
  rw [← Finset.sum_div, div_div]
  congr 1
  simp only [Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_succ,
    Nat.cast_mul]

/-- Number of changed coordinates, viewed as a real number. -/
def hamming {α : Type*} {r : ℕ} (x y : Fin r → α) : ℝ :=
  ∑ i, if x i ≠ y i then 1 else 0

@[simp] theorem hamming_zero {α : Type*} (x y : Fin 0 → α) : hamming x y = 0 := by
  simp [hamming]

@[simp] theorem hamming_cons {α : Type*} {r : ℕ} (a b : α) (x y : Fin r → α) :
    hamming (Fin.cons a x) (Fin.cons b y) = (if a ≠ b then 1 else 0) + hamming x y := by
  simp [hamming, Fin.sum_univ_succ]

theorem hamming_nonneg {α : Type*} {r : ℕ} (x y : Fin r → α) : 0 ≤ hamming x y := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

theorem abs_sub_le_hamming {α : Type*} (r : ℕ) (f : (Fin r → α) → ℝ)
    (hLip : ∀ x i a, |f (Function.update x i a) - f x| ≤ 1)
    (x y : Fin r → α) : |f x - f y| ≤ hamming x y := by
  induction r with
  | zero =>
    have : x = y := Subsingleton.elim _ _
    simp [this]
  | succ r ih =>
    let g : (Fin r → α) → ℝ := fun z => f (Fin.cons (y 0) z)
    have hg : ∀ z i a, |g (Function.update z i a) - g z| ≤ 1 := by
      intro z i a
      simpa only [g, Fin.cons_update] using hLip (Fin.cons (y 0) z) i.succ a
    have ht := ih g hg (Fin.tail x) (Fin.tail y)
    have hh : |f x - f (Fin.cons (y 0) (Fin.tail x))| ≤
        (if x 0 ≠ y 0 then 1 else 0) := by
      by_cases h : x 0 = y 0
      · have he : Fin.cons (y 0) (Fin.tail x) = x := by
          rw [← h, Fin.cons_self_tail]
        simp [h, he]
      · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [abs_sub_comm]
        have he : Function.update x 0 (y 0) = Fin.cons (y 0) (Fin.tail x) := by
          rw [← Fin.update_cons_zero, Fin.cons_self_tail]
        simpa only [he] using hLip x 0 (y 0)
    have htri := abs_sub_le (f x) (f (Fin.cons (y 0) (Fin.tail x))) (f y)
    have hy : g (Fin.tail y) = f y := by simp [g]
    rw [hy] at ht
    have hxy : hamming x y = (if x 0 ≠ y 0 then 1 else 0) + hamming (Fin.tail x) (Fin.tail y) := by
      simpa only [Fin.cons_self_tail] using hamming_cons (x 0) (y 0) (Fin.tail x) (Fin.tail y)
    rw [hxy]
    dsimp [g] at ht
    linarith

/-- A coupling of IID draws with uniform distinct draws, with the usual collision cost. -/
theorem exists_collision_coupling (α : Type*) [Fintype α] [Nonempty α]
    (r : ℕ) (hr : r ≤ Fintype.card α) :
    ∃ p : Law ((Fin r → α) × (Fin r ↪ α)),
      (∀ f : (Fin r → α) → ℝ,
        p.expect (fun z => f z.1) = ((Law.uniform α).iid r).expect f) ∧
      (∀ f : (Fin r ↪ α) → ℝ,
        p.expect (fun z => f z.2) = (orderedLaw α r hr).expect f) ∧
      p.expect (fun z => hamming z.1 z.2) = (r:ℝ) * (r-1) / (2 * Fintype.card α) := by
  induction r with
  | zero =>
    let e : Fin 0 ↪ α := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
    refine ⟨Law.pure (Fin.elim0, e), ?_, ?_, ?_⟩
    · intro f
      simp [expect_iid_zero]
    · intro f
      rw [expect_pure]
      have hf : f = fun _ => f e := by
        funext e'
        congr 1
        exact Subsingleton.elim _ _
      rw [hf, expect_const]
    · simp
  | succ r ih =>
    obtain ⟨p, hp₁, hp₂, hpH⟩ := ih (by omega)
    let q : Law ((Fin (r+1) → α) × (Fin (r+1) ↪ α)) :=
      p.bind (fun z => (Law.repair (freshSet z.2) (freshSet_nonempty z.2 (by omega))).map
        (fun w => (Fin.cons w.1 z.1, consEmbedding z.2 w.2)))
    refine ⟨q, ?_, ?_, ?_⟩
    · intro f
      dsimp [q]
      rw [expect_bind]
      simp_rw [expect_map]
      conv_lhs =>
        arg 2
        ext z
        rw [expect_repair_fst (freshSet z.2) _ (fun a => f (Fin.cons a z.1))]
      rw [expect_comm]
      rw [expect_iid_succ]
      apply expect_congr
      intro a
      exact hp₁ (fun x => f (Fin.cons a x))
    · intro f
      dsimp [q]
      rw [expect_bind]
      simp_rw [expect_map]
      conv_lhs =>
        arg 2
        ext z
        rw [expect_repair_snd (freshSet z.2) _ (fun a => f (consEmbedding z.2 a))]
      rw [orderedLaw_cons_expect hr f]
      exact hp₂ (fun e => @Law.expect (freshSet e) _
        (@Law.uniform (freshSet e) _ (freshSet_nonempty e (by omega)).to_subtype)
        (fun a => f (consEmbedding e a)))
    · dsimp [q]
      rw [expect_bind]
      simp_rw [expect_map, coe_consEmbedding, hamming_cons, expect_add,
        expect_repair_mismatch, expect_const, freshSet_card]
      have hsub : Fintype.card α - (Fintype.card α - r) = r := by omega
      simp_rw [hsub]
      rw [expect_const, hpH]
      have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      push_cast
      field_simp
      ring

end NLA.TR07
