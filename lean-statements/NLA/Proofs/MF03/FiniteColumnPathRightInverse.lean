import NLA.Proofs.MF03.FiniteColumnPathCutExt

/-!
The literal path reconstructed from an existing path's exact column-label
system recovers every intermediate cut and therefore the original chain.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private theorem finitePathAtCut_castTypes {m N : ℕ}
    {X X' Z Z' : StrictRows m} (hX : X = X') (hZ : Z = Z')
    (hType1 : FiniteValidPath m N X Z = FiniteValidPath m N X' Z)
    (hType2 : FiniteValidPath m N X' Z = FiniteValidPath m N X' Z')
    (c : FiniteValidPath m N X Z) (q : ℕ) :
    finitePathAtCut m N X' Z' (Eq.mp hType2 (Eq.mp hType1 c)) q =
      finitePathAtCut m N X Z c q := by
  cases hX
  cases hZ
  cases hType1
  cases hType2
  rfl

/-- The complete reconstructed path visits precisely the explicit cut
tuples calculated from its original column-label system. -/
theorem finiteColumnSystemToPath_atCut {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (hq : q ≤ N) :
    finitePathAtCut m N (finitePathStart m j hj) (finitePathEnd m)
      (finiteColumnSystemToPath hj D) q =
        finiteColumnCutRows hj D q hq := by
  have haux := finiteColumnCutPathAux_atCut hj D N le_rfl q hq
  have htop := finiteColumnCutRows_top hj D
  have hzero := finiteColumnCutRows_zero hj D
  let htype1 :
      FiniteValidPath m N
          (finiteColumnCutRows hj D N le_rfl)
          (finiteColumnCutRows hj D 0 (Nat.zero_le N)) =
        FiniteValidPath m N (finitePathStart m j hj)
          (finiteColumnCutRows hj D 0 (Nat.zero_le N)) :=
    congrArg (fun X => FiniteValidPath m N X
      (finiteColumnCutRows hj D 0 (Nat.zero_le N))) htop
  let htype2 :
      FiniteValidPath m N (finitePathStart m j hj)
          (finiteColumnCutRows hj D 0 (Nat.zero_le N)) =
        FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m) :=
    congrArg (fun Z => FiniteValidPath m N (finitePathStart m j hj) Z) hzero
  have hcast : finiteColumnSystemToPath hj D =
      Eq.mp htype2 (Eq.mp htype1
        (finiteColumnCutPathAux hj D N le_rfl)) := by
    rfl
  rw [hcast]
  exact (finitePathAtCut_castTypes htop hzero htype1 htype2
    (finiteColumnCutPathAux hj D N le_rfl) q).trans haux

/-- Reconstructing a valid path from its exact advance-label column
system returns the original literal chain, for all orders and endpoints. -/
theorem finiteColumnPath_rightInverse {N m j : ℕ} (hj : j ≤ m)
    (c : FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m)) :
    finiteColumnSystemToPath hj
      (finitePathToColumnSystem N m j hj c) = c := by
  let D := finitePathToColumnSystem N m j hj c
  apply finiteValidPath_eq_of_cuts m N
    (finitePathStart m j hj) (finitePathEnd m)
  intro q hq
  rw [finiteColumnSystemToPath_atCut hj D q hq]
  apply Subtype.ext
  funext p
  apply Fin.ext
  have hpath := finitePathAtCut_eq_suffix m N
    (finitePathStart m j hj) (finitePathEnd m) c q hq p
  change finiteColumnCutNat hj D q p =
    ((finitePathAtCut m N (finitePathStart m j hj)
      (finitePathEnd m) c q).1 p).val
  simpa [finiteColumnCutNat, finiteLabelSuffix,
    finiteAdvanceSuffix, D, finitePathToColumnSystem] using hpath

#assert_trust kernel finiteColumnSystemToPath_atCut
#assert_trust kernel finiteColumnPath_rightInverse
#print axioms finiteColumnPath_rightInverse

end NLA.Proofs.MF03
