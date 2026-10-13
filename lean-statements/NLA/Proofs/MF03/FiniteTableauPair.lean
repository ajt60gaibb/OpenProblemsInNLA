import NLA.Proofs.MF03.FiniteTableauTail

/-!
The finite augmented tableau is determined by its rectangular restriction and
its actual bottom-row tuple. This is the injective finite decomposition needed
for the reviewed weighted-tail gate; no weighted inequality is asserted here.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Record the rectangular restriction and the added bottom row. -/
def finiteTableauRestrictPair (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) :
    FiniteTableau (finiteRectShape m) N × (Fin j → Fin N) :=
  (finiteRectRestrict N m j T, finiteBottomTuple N m j hj T)

/-- The restriction and bottom tuple retain every cell of the original tableau. -/
theorem finiteTableauRestrictPair_injective (N m j : ℕ) (hj : j ≤ m) :
    Function.Injective (finiteTableauRestrictPair N m j hj) := by
  intro T U hpair
  have hrect : finiteRectRestrict N m j T = finiteRectRestrict N m j U :=
    congrArg Prod.fst hpair
  have hbottom : finiteBottomTuple N m j hj T =
      finiteBottomTuple N m j hj U := congrArg Prod.snd hpair
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r c
  by_cases hcell : (r, c) ∈ finiteAugShape m j
  · rcases (mem_finiteAugShape m j r c).mp hcell with hrectcell | hbottomcell
    · have hrc : (r, c) ∈ finiteRectShape m :=
        (mem_finiteRectShape m r c).mpr hrectcell
      have hT : (finiteRectRestrict N m j T).1 r c = T.1 r c := by
        change (if (r, c) ∈ finiteRectShape m then T.1 r c else 0) = T.1 r c
        simp [hrc]
      have hU : (finiteRectRestrict N m j U).1 r c = U.1 r c := by
        change (if (r, c) ∈ finiteRectShape m then U.1 r c else 0) = U.1 r c
        simp [hrc]
      have heq := congrArg (fun X : FiniteTableau (finiteRectShape m) N => X.1 r c) hrect
      exact hT.symm.trans (heq.trans hU)
    · rcases hbottomcell with ⟨hr, hc⟩
      have hcj : c < j := by simpa [min_eq_left hj] using hc
      have heq := congrArg Fin.val (congrFun hbottom ⟨c, hcj⟩)
      subst r
      simpa [finiteBottomTuple] using heq
  · exact (T.1.zeros hcell).trans (U.1.zeros hcell).symm

#assert_trust kernel finiteTableauRestrictPair_injective
#print axioms finiteTableauRestrictPair_injective

end NLA.Proofs.MF03
