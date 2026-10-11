import NLA.Proofs.MF03.FiniteColumnSorted

/-!
The exact finite label-set data of an augmented MF-03 path family: fixed
column lengths and the noncollision inequality at every factor-label cut.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Number of labels in a finite set at or above cut `q`. -/
def finiteLabelSuffix (S : Finset ℕ) (q : ℕ) : ℕ :=
  (S.filter fun k => q ≤ k).card

/-- The source-locked column-set form of the augmented tableau conditions. -/
structure FiniteColumnSystem (N m j : ℕ) where
  labels : Fin m → Finset ℕ
  label_lt : ∀ p : Fin m, ∀ k ∈ labels p, k < N
  card_eq : ∀ p : Fin m,
    (labels p).card = if p.val < j then m + 1 else m
  noncollision : ∀ (q : ℕ), q ≤ N →
    ∀ (p : Fin m) (hp : p.val + 1 < m),
      finiteLabelSuffix (labels p) q ≤
        finiteLabelSuffix (labels ⟨p.val + 1, hp⟩) q +
          (if p.val + 1 = j then 1 else 0)

/-- A valid path chain yields its exact family of advance-label sets. -/
def finitePathToColumnSystem (N m j : ℕ) (hj : j ≤ m)
    (c : FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m)) :
    FiniteColumnSystem N m j where
  labels := fun p => finiteAdvanceLabels m N
    (finitePathStart m j hj) (finitePathEnd m) c p
  label_lt := by
    intro p k hk
    exact finiteAdvanceLabels_lt m N
      (finitePathStart m j hj) (finitePathEnd m) c p k hk
  card_eq := finiteAdvanceLabels_card_endpoint N m j hj c
  noncollision := by
    intro q hq p hp
    change finiteAdvanceSuffix m N (finitePathStart m j hj)
      (finitePathEnd m) c p q ≤
      finiteAdvanceSuffix m N (finitePathStart m j hj)
        (finitePathEnd m) c ⟨p.val + 1, hp⟩ q +
          (if p.val + 1 = j then 1 else 0)
    exact finiteAdvanceSuffix_noncollision_endpoint N m j hj c q hq p hp

#assert_trust kernel finitePathToColumnSystem
#print axioms finitePathToColumnSystem

end NLA.Proofs.MF03
