import NLA.Proofs.MF03.FinitePathCuts

/-!
Enumerate a finite advance-label set in strict increasing order. The
suffix count is unchanged by that enumeration, which is the bridge from
path cut inequalities to tableau row inequalities.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The unique increasing enumeration of a finite label set of size `n`. -/
noncomputable def finiteSortedColumn {n : ℕ}
    (S : Finset ℕ) (hcard : S.card = n) : Fin n → ℕ :=
  S.orderEmbOfFin hcard

theorem finiteSortedColumn_strictMono {n : ℕ}
    (S : Finset ℕ) (hcard : S.card = n) :
    StrictMono (finiteSortedColumn S hcard) :=
  (S.orderEmbOfFin hcard).strictMono

/-- Sorting a label set does not change the count at or above any cut. -/
theorem finiteSortedColumn_suffix {n : ℕ}
    (S : Finset ℕ) (hcard : S.card = n) (q : ℕ) :
    finiteColumnSuffix (finiteSortedColumn S hcard) q =
      (S.filter fun k => q ≤ k).card := by
  classical
  let e : Fin n ↪o ℕ := S.orderEmbOfFin hcard
  change (((Finset.univ : Finset (Fin n)).filter
      fun r => q ≤ e r).card) = (S.filter fun k => q ≤ k).card
  rw [← Finset.image_orderEmbOfFin_univ S hcard]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ e.injective]

/-- Every sorted label is one of the original labels. -/
theorem finiteSortedColumn_mem {n : ℕ}
    (S : Finset ℕ) (hcard : S.card = n) (r : Fin n) :
    finiteSortedColumn S hcard r ∈ S :=
  Finset.orderEmbOfFin_mem S hcard r

/-- The sorted column contains precisely the original finite set. -/
theorem finiteSortedColumn_image {n : ℕ}
    (S : Finset ℕ) (hcard : S.card = n) :
    (Finset.univ : Finset (Fin n)).image (finiteSortedColumn S hcard) = S :=
  Finset.image_orderEmbOfFin_univ S hcard

#assert_trust kernel finiteSortedColumn_suffix
#assert_trust kernel finiteSortedColumn_image
#print axioms finiteSortedColumn_suffix

end NLA.Proofs.MF03
