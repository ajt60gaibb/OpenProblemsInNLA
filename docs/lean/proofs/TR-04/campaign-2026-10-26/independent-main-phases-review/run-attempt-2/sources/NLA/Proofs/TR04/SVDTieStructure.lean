import NLA.Proofs.TR04.SVDTieError

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

theorem card_filter_fin_lt {p n : ℕ} (hn : n ≤ p) :
    (Finset.univ.filter (fun i : Fin p => i.val < n)).card = n := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (prefixSubtypeEquiv hn)).trans (Fintype.card_fin n)

/-- A lower subset of a finite linear order is exactly its cardinal-length prefix. -/
theorem lower_predicate_iff_lt_card {p : ℕ} (P : Fin p → Prop) [DecidablePred P]
    (hP : ∀ i j, i ≤ j → P j → P i) (i : Fin p) :
    P i ↔ i.val < (Finset.univ.filter P).card := by
  constructor
  · intro hi
    have hs : Finset.univ.filter (fun j : Fin p => j.val < i.val + 1) ⊆
        Finset.univ.filter P := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hP j i (Fin.le_iff_val_le_val.mpr (by omega)) hi
    have hc := Finset.card_le_card hs
    rw [card_filter_fin_lt (by omega)] at hc
    omega
  · intro hi
    by_contra hn
    have hs : Finset.univ.filter P ⊆
        Finset.univ.filter (fun j : Fin p => j.val < i.val) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hji
      exact hn (hP i j (Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hji)) hj)
    have hc := Finset.card_le_card hs
    rw [card_filter_fin_lt i.isLt.le] at hc
    omega

/-- Complete consecutive threshold block, with the number of retained tied
directions dictated by the original positive rank allowance. -/
structure TieStructure {p : ℕ} (sigma : Fin p → ℝ) (a : Fin p) where
  above : ℕ
  tied : ℕ
  take : ℕ
  fits : above + tied ≤ p
  take_pos : 1 ≤ take
  take_le : take ≤ tied
  rank_eq : above + take = a.val + 1
  above_iff : ∀ k, sigma a < sigma k ↔ k.val < above
  equal_iff : ∀ k, sigma k = sigma a ↔ above ≤ k.val ∧ k.val < above + tied

theorem exists_tieStructure {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (a : Fin p) : Nonempty (TieStructure sigma a) := by
  classical
  let H := Finset.univ.filter (fun k : Fin p => sigma a < sigma k)
  let G := Finset.univ.filter (fun k : Fin p => sigma a ≤ sigma k)
  let h := H.card
  let b := G.card
  have hH (k : Fin p) : sigma a < sigma k ↔ k.val < h := by
    exact lower_predicate_iff_lt_card (fun i => sigma a < sigma i)
      (fun i j hij hj => lt_of_lt_of_le hj (hord hij)) k
  have hG (k : Fin p) : sigma a ≤ sigma k ↔ k.val < b := by
    exact lower_predicate_iff_lt_card (fun i => sigma a ≤ sigma i)
      (fun i j hij hj => hj.trans (hord hij)) k
  have hhb : h ≤ b := Finset.card_le_card (by
    intro k hk
    simp only [H, G, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.le)
  have hha : h ≤ a.val := by
    have hn : ¬ sigma a < sigma a := lt_irrefl _
    rw [hH] at hn
    omega
  have hab : a.val < b := (hG a).mp le_rfl
  have hbp : b ≤ p := by
    have hc := Finset.card_le_card (Finset.filter_subset (fun k : Fin p => sigma a ≤ sigma k) Finset.univ)
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  refine ⟨{ above := h
            tied := b - h
            take := a.val + 1 - h
            fits := by omega
            take_pos := by omega
            take_le := by omega
            rank_eq := by omega
            above_iff := hH
            equal_iff := ?_ }⟩
  intro k
  have heq : h + (b - h) = b := by omega
  rw [heq]
  constructor
  · intro hk
    have hkG : k.val < b := (hG k).mp (by rw [hk])
    have hkH : ¬ k.val < h := by
      intro hh
      have := (hH k).mpr hh
      rw [hk] at this
      exact (lt_irrefl _) this
    exact ⟨Nat.le_of_not_gt hkH, hkG⟩
  · rintro ⟨hkH, hkG⟩
    have hl : sigma a ≤ sigma k := (hG k).mpr hkG
    have hu : sigma k ≤ sigma a := by
      by_contra hn
      have := (hH k).mp (lt_of_not_ge hn)
      omega
    exact le_antisymm hu hl

theorem TieStructure.tied_pos {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) : 0 < T.tied :=
  lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) T.take_pos) T.take_le

instance {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p} (T : TieStructure sigma a) : NeZero T.tied :=
  ⟨Nat.ne_of_gt T.tied_pos⟩

theorem TieStructure.equal_embedding {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (i : Fin T.tied) :
    sigma (tieEmbedding T.above T.tied T.fits i) = sigma a := by
  apply (T.equal_iff _).mpr
  change T.above ≤ T.above + i.val ∧ T.above + i.val < T.above + T.tied
  omega

#assert_trust kernel exists_tieStructure
#assert_trust kernel TieStructure.equal_embedding
#print axioms exists_tieStructure
end NLA.Proofs.TR04.SVD
