import NLA.Proofs.MF03.FiniteTableauColumnProduct
import NLA.Proofs.MF03.FiniteColumnPathEquiv
import NLA.Proofs.MF03.FinitePathWeight

/-!
The exact finite valid-path weight equals the original augmented-tableau
summand under the literal path-to-column-to-tableau map.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

/-- All actual-column label products give exactly the original rectangular
and bottom-row tableau weight; no sentinel or extra factor occurs. -/
theorem finiteTableau_columnProducts_eq_weights {N m j : ℕ} (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) :
    (∏ p : Fin m,
      ∏ k ∈ finiteTableauActualLabels T p, cosineFactor (k + 1)) =
      finiteRectWeight m T.1 * finiteBottomWeight j m T.1 := by
  classical
  calc
    (∏ p : Fin m,
      ∏ k ∈ finiteTableauActualLabels T p, cosineFactor (k + 1)) =
        ∏ p : Fin m,
          ((∏ r ∈ Finset.range m, cosineFactor (T.1 r p.val + 1)) *
            (if p.val < j then cosineFactor (T.1 m p.val + 1) else 1)) := by
              apply Finset.prod_congr rfl
              intro p _
              exact finiteTableauActualLabels_product hj T p
    _ = (∏ p : Fin m,
          ∏ r ∈ Finset.range m, cosineFactor (T.1 r p.val + 1)) *
        (∏ p : Fin m,
          if p.val < j then cosineFactor (T.1 m p.val + 1) else 1) := by
            rw [← Finset.prod_mul_distrib]
    _ = finiteRectWeight m T.1 * finiteBottomWeight j m T.1 := by
          congr 1
          · calc
              (∏ p : Fin m,
                  ∏ r ∈ Finset.range m, cosineFactor (T.1 r p.val + 1)) =
                  ∏ p ∈ Finset.range m,
                    ∏ r ∈ Finset.range m, cosineFactor (T.1 r p + 1) :=
                Fin.prod_univ_eq_prod_range
                  (fun p : ℕ => ∏ r ∈ Finset.range m,
                    cosineFactor (T.1 r p + 1)) m
              _ = finiteRectWeight m T.1 := by
                unfold finiteRectWeight
                exact Finset.prod_comm
          · calc
              (∏ p : Fin m,
                  if p.val < j then cosineFactor (T.1 m p.val + 1) else 1) =
                  ∏ p ∈ Finset.range m,
                    if p < j then cosineFactor (T.1 m p + 1) else 1 :=
                Fin.prod_univ_eq_prod_range
                  (fun p : ℕ => if p < j then cosineFactor (T.1 m p + 1) else 1) m
              _ = finiteBottomWeight j m T.1 := by
                unfold finiteBottomWeight
                rw [← Finset.prod_filter]
                have hfilt : (Finset.range m).filter (fun p => p < j) =
                    Finset.range j := by
                  ext p
                  simp only [Finset.mem_filter, Finset.mem_range]
                  omega
                rw [hfilt]

/-- Exact weight of a literal path equals the original tableau summand
of its actual advance-label tableau. -/
theorem finiteValidPathWeight_eq_tableauWeight {N m j : ℕ} (hj : j ≤ m)
    (c : FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m)) :
    let D := finitePathToColumnSystem N m j hj c
    let T := finiteColumnSystemToTableau D hj
    finiteValidPathWeight m N (finitePathStart m j hj) (finitePathEnd m) c =
      finiteRectWeight m T.1 * finiteBottomWeight j m T.1 := by
  dsimp only
  let D := finitePathToColumnSystem N m j hj c
  let T := finiteColumnSystemToTableau D hj
  calc
    finiteValidPathWeight m N (finitePathStart m j hj) (finitePathEnd m) c =
      ∏ p : Fin m,
        ∏ k ∈ finiteAdvanceLabels m N
          (finitePathStart m j hj) (finitePathEnd m) c p,
            cosineFactor (k + 1) :=
      finiteValidPathWeight_eq_labelProducts m N _ _ c
    _ = ∏ p : Fin m,
          ∏ k ∈ finiteTableauActualLabels T p, cosineFactor (k + 1) := by
      apply Finset.prod_congr rfl
      intro p _
      have hlabels := finiteColumnSystem_tableau_actualLabels hj D p
      change finiteTableauActualLabels T p =
        finiteAdvanceLabels m N (finitePathStart m j hj)
          (finitePathEnd m) c p at hlabels
      rw [hlabels]
    _ = finiteRectWeight m T.1 * finiteBottomWeight j m T.1 :=
      finiteTableau_columnProducts_eq_weights hj T

#assert_trust kernel finiteTableau_columnProducts_eq_weights
#assert_trust kernel finiteValidPathWeight_eq_tableauWeight
#print axioms finiteValidPathWeight_eq_tableauWeight

end NLA.Proofs.MF03
