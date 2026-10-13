import NLA.Proofs.MF03.FiniteColumnCuts

/-!
Read a valid chain at every factor-label cut, and express its ordered
positions by counts of advance labels at or above that cut.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Ordered path positions after processing every factor with label at
least `q`; at `q=N` this is the original starting tuple. -/
def finitePathAtCut (m : ℕ) :
    (N : ℕ) → (X Z : StrictRows m) →
      FiniteValidPath m N X Z → ℕ → StrictRows m
  | 0, X, _, _, _ => X
  | N + 1, X, Z, ⟨Y, ⟨_, tail⟩⟩, q =>
      if q = N + 1 then X else finitePathAtCut m N Y Z tail q

/-- The number of path-`p` advances already processed at cut `q`. -/
def finiteAdvanceSuffix (m N : ℕ) (X Z : StrictRows m)
    (c : FiniteValidPath m N X Z) (p : Fin m) (q : ℕ) : ℕ :=
  ((finiteAdvanceLabels m N X Z c p).filter fun k => q ≤ k).card

/-- The position at a cut is its starting position plus exactly the
number of advances whose factor labels have been processed. -/
theorem finitePathAtCut_eq_suffix (m : ℕ) :
    ∀ (N : ℕ) (X Z : StrictRows m)
      (c : FiniteValidPath m N X Z) (q : ℕ), q ≤ N →
      ∀ p : Fin m,
        (X.1 p).val + finiteAdvanceSuffix m N X Z c p q =
          ((finitePathAtCut m N X Z c q).1 p).val := by
  intro N
  induction N with
  | zero =>
      intro X Z c q hq p
      have hq0 : q = 0 := by omega
      subst q
      simp [finiteAdvanceSuffix, finiteAdvanceLabels, finitePathAtCut]
  | succ N ih =>
      intro X Z c q hq p
      rcases c with ⟨Y, ⟨hvalid, tail⟩⟩
      by_cases htop : q = N + 1
      · have hzero :
          finiteAdvanceSuffix m (N + 1) X Z
            ⟨Y, ⟨hvalid, tail⟩⟩ p q = 0 := by
          unfold finiteAdvanceSuffix
          apply Finset.card_eq_zero.mpr
          ext k
          constructor
          · intro hk
            have hkmem := (Finset.mem_filter.mp hk).1
            have hkq := (Finset.mem_filter.mp hk).2
            have hlt := finiteAdvanceLabels_lt m (N + 1) X Z
              ⟨Y, ⟨hvalid, tail⟩⟩ p k hkmem
            exact False.elim (by omega)
          · intro hk
            simp at hk
        subst q
        simpa [finitePathAtCut] using hzero
      · have hqN : q ≤ N := by omega
        have htail := ih Y Z tail q hqN p
        have hgeom := hvalid.down p
        simp only [finitePathAtCut, if_neg htop]
        change (X.1 p).val +
          finiteAdvanceSuffix m (N + 1) X Z
            ⟨Y, ⟨hvalid, tail⟩⟩ p q =
          ((finitePathAtCut m N Y Z tail q).1 p).val
        by_cases hadvance : (Y.1 p).val = (X.1 p).val + 1
        · have hfresh :
            N ∉ (finiteAdvanceLabels m N Y Z tail p).filter
              (fun k => q ≤ k) := by
            intro hN
            have hmem := (Finset.mem_filter.mp hN).1
            have hlt := finiteAdvanceLabels_lt m N Y Z tail p N hmem
            omega
          have hsuffix :
              finiteAdvanceSuffix m (N + 1) X Z
                ⟨Y, ⟨hvalid, tail⟩⟩ p q =
                finiteAdvanceSuffix m N Y Z tail p q + 1 := by
            simp [finiteAdvanceSuffix, finiteAdvanceLabels,
              hadvance, Finset.filter_insert, hqN,
              Finset.card_insert_of_notMem hfresh]
          rw [hsuffix]
          omega
        · have hstay : (Y.1 p).val = (X.1 p).val :=
            hgeom.resolve_right hadvance
          have hsuffix :
              finiteAdvanceSuffix m (N + 1) X Z
                ⟨Y, ⟨hvalid, tail⟩⟩ p q =
                finiteAdvanceSuffix m N Y Z tail p q := by
            simp [finiteAdvanceSuffix, finiteAdvanceLabels, hadvance]
          rw [hsuffix]
          omega

/-- Strictly ordered intermediate positions give the exact adjacent
noncollision inequality at every label cut. -/
theorem finiteAdvanceSuffix_noncollision (m N : ℕ)
    (X Z : StrictRows m) (c : FiniteValidPath m N X Z)
    (q : ℕ) (hq : q ≤ N) (p : Fin m) (hp : p.val + 1 < m) :
    (X.1 p).val + finiteAdvanceSuffix m N X Z c p q <
      (X.1 ⟨p.val + 1, hp⟩).val +
        finiteAdvanceSuffix m N X Z c ⟨p.val + 1, hp⟩ q := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  have hlt : p < p' := by simp [p', Fin.lt_def]
  have hstrict := (finitePathAtCut m N X Z c q).2 hlt
  have hl := finitePathAtCut_eq_suffix m N X Z c q hq p
  have hr := finitePathAtCut_eq_suffix m N X Z c q hq p'
  change (X.1 p).val + finiteAdvanceSuffix m N X Z c p q <
    (X.1 p').val + finiteAdvanceSuffix m N X Z c p' q
  omega

/-- For the original augmented-minor endpoints, the only permitted
suffix-count excess is the one extra starting gap across omitted row `j`. -/
theorem finiteAdvanceSuffix_noncollision_endpoint (N m j : ℕ)
    (hj : j ≤ m)
    (c : FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m))
    (q : ℕ) (hq : q ≤ N) (p : Fin m) (hp : p.val + 1 < m) :
    finiteAdvanceSuffix m N (finitePathStart m j hj)
        (finitePathEnd m) c p q ≤
      finiteAdvanceSuffix m N (finitePathStart m j hj)
        (finitePathEnd m) c ⟨p.val + 1, hp⟩ q +
        (if p.val + 1 = j then 1 else 0) := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  have hnc := finiteAdvanceSuffix_noncollision m N
    (finitePathStart m j hj) (finitePathEnd m) c q hq p hp
  have hgap :
      ((finitePathStart m j hj).1 p').val =
        ((finitePathStart m j hj).1 p).val +
          (if p.val + 1 = j then 2 else 1) := by
    change (if p.val + 1 < j then p.val + 1 else p.val + 2) =
      (if p.val < j then p.val else p.val + 1) +
        (if p.val + 1 = j then 2 else 1)
    split_ifs <;> omega
  change finiteAdvanceSuffix m N (finitePathStart m j hj)
      (finitePathEnd m) c p q ≤
    finiteAdvanceSuffix m N (finitePathStart m j hj)
      (finitePathEnd m) c p' q +
      (if p.val + 1 = j then 1 else 0)
  change ((finitePathStart m j hj).1 p).val +
    finiteAdvanceSuffix m N (finitePathStart m j hj)
      (finitePathEnd m) c p q <
    ((finitePathStart m j hj).1 p').val +
    finiteAdvanceSuffix m N (finitePathStart m j hj)
      (finitePathEnd m) c p' q at hnc
  rw [hgap] at hnc
  split_ifs at hnc ⊢ <;> omega

#assert_trust kernel finitePathAtCut_eq_suffix
#assert_trust kernel finiteAdvanceSuffix_noncollision_endpoint
#print axioms finiteAdvanceSuffix_noncollision_endpoint

end NLA.Proofs.MF03
