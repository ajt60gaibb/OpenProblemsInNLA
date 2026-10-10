import NLA.Proofs.MF03.FiniteColumnCutPositions

/-!
The explicit cut-position formula has the exact original MF-03 endpoint
tuples. Crossing one factor label is stationary or one advance in every
coordinate, with no change of factor-label order.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- At cut `N`, no actual advance label has been processed. -/
theorem finiteColumnCutRows_top {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    finiteColumnCutRows hj D N le_rfl = finitePathStart m j hj := by
  apply Subtype.ext
  funext p
  apply Fin.ext
  change finiteColumnCutNat hj D N p =
    ((finitePathStart m j hj).1 p).val
  unfold finiteColumnCutNat
  rw [finiteLabelSuffix_top N (D.labels p) (D.label_lt p)]
  omega

/-- At cut zero, every actual label has been processed, giving the exact
terminal tuple. -/
theorem finiteColumnCutRows_zero {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    finiteColumnCutRows hj D 0 (Nat.zero_le N) = finitePathEnd m := by
  apply Subtype.ext
  funext p
  apply Fin.ext
  change finiteColumnCutNat hj D 0 p =
    ((finitePathEnd m).1 p).val
  unfold finiteColumnCutNat
  rw [finiteLabelSuffix_zero, D.card_eq p]
  have hdisp := finitePath_advance_count m j hj p
  have hstart := finiteColumn_start_le_end m j hj p
  omega

/-- The move from cut `q+1` to cut `q` is a valid stationary or one-step
transition. It is the transition carrying factor label `q`. -/
theorem finiteColumnCutRows_step {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (hq : q + 1 ≤ N) :
    finiteValidStep m
      (finiteColumnCutRows hj D (q + 1) hq)
      (finiteColumnCutRows hj D q (by omega)) := by
  intro p
  have hstep := finiteLabelSuffix_step (D.labels p) q
  change finiteColumnCutNat hj D q p =
      finiteColumnCutNat hj D (q + 1) p ∨
    finiteColumnCutNat hj D q p =
      finiteColumnCutNat hj D (q + 1) p + 1
  unfold finiteColumnCutNat
  by_cases hmem : q ∈ D.labels p
  · right
    simp [hmem] at hstep
    omega
  · left
    simp [hmem] at hstep
    omega

#assert_trust kernel finiteColumnCutRows_top
#assert_trust kernel finiteColumnCutRows_zero
#assert_trust kernel finiteColumnCutRows_step
#print axioms finiteColumnCutRows_step

end NLA.Proofs.MF03
