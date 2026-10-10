import NLA.Proofs.MF03.FinitePathEndpoint

/-!
Collect the exact factor labels at which a valid finite MF-03 path advances.
These are zero-based tableau labels, before sorting into columns.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Factor labels at which path `p` advances in a literal valid chain.
The first transition in a length-`N+1` chain has label `N`. -/
def finiteAdvanceLabels (m : ℕ) :
    (N : ℕ) → (X Z : StrictRows m) →
      FiniteValidPath m N X Z → Fin m → Finset ℕ
  | 0, _, _, _, _ => ∅
  | N + 1, X, Z, ⟨Y, ⟨_, c⟩⟩, p =>
      if (Y.1 p).val = (X.1 p).val + 1 then
        insert N (finiteAdvanceLabels m N Y Z c p)
      else finiteAdvanceLabels m N Y Z c p

/-- Every advance label belongs to the original factor range. -/
theorem finiteAdvanceLabels_lt (m : ℕ) :
    ∀ (N : ℕ) (X Z : StrictRows m)
      (c : FiniteValidPath m N X Z) (p : Fin m) (k : ℕ),
      k ∈ finiteAdvanceLabels m N X Z c p → k < N := by
  intro N
  induction N with
  | zero =>
      intro X Z c p k hk
      simp [finiteAdvanceLabels] at hk
  | succ N ih =>
      intro X Z c p k hk
      rcases c with ⟨Y, ⟨h, tail⟩⟩
      by_cases hstep : (Y.1 p).val = (X.1 p).val + 1
      · simp only [finiteAdvanceLabels, if_pos hstep,
          Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · omega
        · exact Nat.lt_succ_of_lt (ih Y Z tail p k hk)
      · simp only [finiteAdvanceLabels, if_neg hstep] at hk
        exact Nat.lt_succ_of_lt (ih Y Z tail p k hk)

/-- The number of advance labels is the exact endpoint displacement. -/
theorem finiteAdvanceLabels_card (m : ℕ) :
    ∀ (N : ℕ) (X Z : StrictRows m)
      (c : FiniteValidPath m N X Z) (p : Fin m),
      (X.1 p).val + (finiteAdvanceLabels m N X Z c p).card =
        (Z.1 p).val := by
  intro N
  induction N with
  | zero =>
      intro X Z c p
      obtain ⟨h⟩ := c
      subst Z
      simp [finiteAdvanceLabels]
  | succ N ih =>
      intro X Z c p
      rcases c with ⟨Y, ⟨hvalid, tail⟩⟩
      have htail := ih Y Z tail p
      have hgeom := hvalid.down p
      by_cases hstep : (Y.1 p).val = (X.1 p).val + 1
      · have hfresh : N ∉ finiteAdvanceLabels m N Y Z tail p := by
          intro hN
          have hlt := finiteAdvanceLabels_lt m N Y Z tail p N hN
          omega
        simp only [finiteAdvanceLabels, if_pos hstep,
          Finset.card_insert_of_notMem hfresh]
        omega
      · have hstationary : (Y.1 p).val = (X.1 p).val :=
          hgeom.resolve_right hstep
        simp only [finiteAdvanceLabels, if_neg hstep]
        omega

/-- At the augmented-minor endpoints, the label-set size is exactly the
corresponding augmented tableau column length. -/
theorem finiteAdvanceLabels_card_endpoint (N m j : ℕ) (hj : j ≤ m)
    (c : FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m))
    (p : Fin m) :
    (finiteAdvanceLabels m N (finitePathStart m j hj)
      (finitePathEnd m) c p).card =
        if p.val < j then m + 1 else m := by
  have hcount := finiteAdvanceLabels_card m N
    (finitePathStart m j hj) (finitePathEnd m) c p
  have hdiff := finitePath_advance_count m j hj p
  omega

#assert_trust kernel finiteAdvanceLabels_lt
#assert_trust kernel finiteAdvanceLabels_card
#assert_trust kernel finiteAdvanceLabels_card_endpoint
#print axioms finiteAdvanceLabels_card
#print axioms finiteAdvanceLabels_card_endpoint

end NLA.Proofs.MF03
