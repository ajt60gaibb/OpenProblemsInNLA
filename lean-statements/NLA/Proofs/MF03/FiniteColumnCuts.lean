import NLA.Proofs.MF03.FiniteColumnOrder

/-!
Exact equivalence between weak tableau rows and suffix-count inequalities
at every zero-based factor-label cut. These are the numerical inequalities
that encode strict noncollision of adjacent finite paths.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Count column entries at or above a zero-based factor-label cut. -/
def finiteColumnSuffix {n : ℕ} (a : Fin n → ℕ) (q : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun r => q ≤ a r).card

theorem finiteColumnPrefix_add_suffix {n : ℕ}
    (a : Fin n → ℕ) (q : ℕ) :
    finiteColumnPrefix a q + finiteColumnSuffix a q = n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (p := fun r => a r < q)
  simpa [finiteColumnPrefix, finiteColumnSuffix, not_lt] using h

/-- Equal-length columns have weak tableau rows exactly when the left
column has no more labels above any cut than the right column. -/
theorem finiteColumnOrder_iff_suffix_same (n : ℕ)
    (a b : Fin n → ℕ) (ha : StrictMono a) (hb : StrictMono b) :
    (∀ r : Fin n, a r ≤ b r) ↔
      ∀ q : ℕ, finiteColumnSuffix a q ≤ finiteColumnSuffix b q := by
  constructor
  · intro hab q
    have hp := (finiteColumnOrder_iff_prefix_same n a b ha hb).mp hab q
    have ha' := finiteColumnPrefix_add_suffix a q
    have hb' := finiteColumnPrefix_add_suffix b q
    omega
  · intro hs
    apply (finiteColumnOrder_iff_prefix_same n a b ha hb).mpr
    intro q
    have hq := hs q
    have ha' := finiteColumnPrefix_add_suffix a q
    have hb' := finiteColumnPrefix_add_suffix b q
    omega

/-- Across the one extra left bottom cell, the permissible suffix-count
excess is exactly one. -/
theorem finiteColumnOrder_iff_suffix_extra (n : ℕ)
    (a : Fin (n + 1) → ℕ) (b : Fin n → ℕ)
    (ha : StrictMono a) (hb : StrictMono b) :
    (∀ r : Fin n, a (Fin.castSucc r) ≤ b r) ↔
      ∀ q : ℕ, finiteColumnSuffix a q ≤ finiteColumnSuffix b q + 1 := by
  constructor
  · intro hab q
    have hp := (finiteColumnOrder_iff_prefix_extra n a b ha hb).mp hab q
    have ha' := finiteColumnPrefix_add_suffix a q
    have hb' := finiteColumnPrefix_add_suffix b q
    omega
  · intro hs
    apply (finiteColumnOrder_iff_prefix_extra n a b ha hb).mpr
    intro q
    have hq := hs q
    have ha' := finiteColumnPrefix_add_suffix a q
    have hb' := finiteColumnPrefix_add_suffix b q
    omega

#assert_trust kernel finiteColumnPrefix_add_suffix
#assert_trust kernel finiteColumnOrder_iff_suffix_same
#assert_trust kernel finiteColumnOrder_iff_suffix_extra
#print axioms finiteColumnOrder_iff_suffix_same
#print axioms finiteColumnOrder_iff_suffix_extra

end NLA.Proofs.MF03
