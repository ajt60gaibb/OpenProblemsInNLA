import NLA.Proofs.MF03.FiniteTableauPair

/-!
Exact weight factorization through the reviewed injective finite-tableau
restriction pair. This is a finite combinatorial gate; the weighted tail
inequality and the determinant/tableau identity remain separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

noncomputable def finiteBottomTupleWeight (N j : ℕ) (b : Fin j → Fin N) : ℝ :=
  ∏ c : Fin j, cosineFactor ((b c).val + 1)

theorem finiteRectWeight_restrict (N m j : ℕ)
    (T : FiniteTableau (finiteAugShape m j) N) :
    finiteRectWeight m T.1 =
      finiteRectWeight m (finiteRectRestrict N m j T).1 := by
  unfold finiteRectWeight
  apply Finset.prod_congr rfl
  intro r hr
  apply Finset.prod_congr rfl
  intro c hc
  have hcell : (r, c) ∈ finiteRectShape m :=
    (mem_finiteRectShape m r c).mpr
      ⟨Finset.mem_range.mp hr, Finset.mem_range.mp hc⟩
  change cosineFactor (T.1 r c + 1) =
    cosineFactor ((if (r, c) ∈ finiteRectShape m then T.1 r c else 0) + 1)
  simp [hcell]

theorem finiteBottomWeight_eq_tupleWeight (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) :
    finiteBottomWeight j m T.1 =
      finiteBottomTupleWeight N j (finiteBottomTuple N m j hj T) := by
  unfold finiteBottomWeight finiteBottomTupleWeight
  rw [← Fin.prod_univ_eq_prod_range
    (fun c : ℕ => cosineFactor (T.1 m c + 1)) j]
  apply Finset.prod_congr rfl
  intro c hc
  simp [finiteBottomTuple]

theorem finiteAugTableau_weight_factor (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) :
    finiteRectWeight m T.1 * finiteBottomWeight j m T.1 =
      finiteRectWeight m (finiteTableauRestrictPair N m j hj T).1.1 *
        finiteBottomTupleWeight N j (finiteTableauRestrictPair N m j hj T).2 := by
  rw [finiteRectWeight_restrict N m j T,
    finiteBottomWeight_eq_tupleWeight N m j hj T]
  rfl

#assert_trust kernel finiteRectWeight_restrict
#assert_trust kernel finiteBottomWeight_eq_tupleWeight
#assert_trust kernel finiteAugTableau_weight_factor

end NLA.Proofs.MF03
