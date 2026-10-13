import NLA.Proofs.MF03.FinitePathWeight

/-!
A generic finite-order-statistics lemma for adjacent tableau columns. It is
independent of any fixed order or cosine value. The row and noncollision
inequalities are compared through counts below each label cut.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Count column entries strictly below a zero-based label cut. -/
def finiteColumnPrefix {n : ℕ} (a : Fin n → ℕ) (q : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun r => a r < q).card

private theorem finiteColumnPrefix_rank {n : ℕ}
    (a : Fin n → ℕ) (ha : StrictMono a) (r : Fin n) (q : ℕ) :
    r.val < finiteColumnPrefix a q ↔ a r < q := by
  classical
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro i j hji hi
  exact lt_of_le_of_lt (ha.monotone hji) hi

/-- For equally long strictly increasing columns, rowwise weak increase is
equivalent to dominance of every prefix count. -/
theorem finiteColumnOrder_iff_prefix_same (n : ℕ)
    (a b : Fin n → ℕ) (ha : StrictMono a) (hb : StrictMono b) :
    (∀ r : Fin n, a r ≤ b r) ↔
      ∀ q : ℕ, finiteColumnPrefix b q ≤ finiteColumnPrefix a q := by
  classical
  constructor
  · intro hab q
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact lt_of_le_of_lt (hab r) hr
  · intro hprefix r
    by_contra hnot
    have hbr : b r < a r := lt_of_not_ge hnot
    have hbcount : r.val < finiteColumnPrefix b (a r) :=
      (finiteColumnPrefix_rank b hb r (a r)).2 hbr
    have hanot : ¬ r.val < finiteColumnPrefix a (a r) := by
      intro hlt
      have := (finiteColumnPrefix_rank a ha r (a r)).1 hlt
      exact (lt_irrefl (a r)) this
    have hq := hprefix (a r)
    omega

/-- If the left column has one extra bottom cell, the same prefix-count
criterion characterizes rowwise weak increase on the common rows. -/
theorem finiteColumnOrder_iff_prefix_extra (n : ℕ)
    (a : Fin (n + 1) → ℕ) (b : Fin n → ℕ)
    (ha : StrictMono a) (hb : StrictMono b) :
    (∀ r : Fin n, a (Fin.castSucc r) ≤ b r) ↔
      ∀ q : ℕ, finiteColumnPrefix b q ≤ finiteColumnPrefix a q := by
  classical
  constructor
  · intro hab q
    let s : Finset (Fin n) :=
      (Finset.univ : Finset (Fin n)).filter fun r => b r < q
    let t : Finset (Fin (n + 1)) :=
      (Finset.univ : Finset (Fin (n + 1))).filter fun r => a r < q
    change s.card ≤ t.card
    calc
      s.card = (s.image Fin.castSucc).card :=
        (Finset.card_image_of_injective s (Fin.castSucc_injective n)).symm
      _ ≤ t.card := by
        apply Finset.card_le_card
        intro r hr
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        have hbi : b i < q := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, lt_of_le_of_lt (hab i) hbi⟩
  · intro hprefix r
    by_contra hnot
    have hbr : b r < a (Fin.castSucc r) := lt_of_not_ge hnot
    have hbcount : r.val < finiteColumnPrefix b (a (Fin.castSucc r)) :=
      (finiteColumnPrefix_rank b hb r (a (Fin.castSucc r))).2 hbr
    have hanot : ¬ r.val < finiteColumnPrefix a (a (Fin.castSucc r)) := by
      intro hlt
      have := (finiteColumnPrefix_rank a ha (Fin.castSucc r)
        (a (Fin.castSucc r))).1 (by simpa using hlt)
      exact (lt_irrefl (a (Fin.castSucc r))) this
    have hq := hprefix (a (Fin.castSucc r))
    omega

#assert_trust kernel finiteColumnOrder_iff_prefix_same
#assert_trust kernel finiteColumnOrder_iff_prefix_extra
#print axioms finiteColumnOrder_iff_prefix_same
#print axioms finiteColumnOrder_iff_prefix_extra

end NLA.Proofs.MF03
