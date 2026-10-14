import NLA.Proofs.MF03.FiniteAugDetTableau

/-!
At zero augmented bottom length, the original Young diagram, weight,
and finite determinant are exactly the original rectangular objects.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The augmented shape with no bottom cells is literally the original
rectangular Young diagram. -/
theorem finiteAugShape_zero (m : ℕ) :
    finiteAugShape m 0 = finiteRectShape m := by
  ext ⟨r, c⟩
  simp [mem_finiteAugShape, mem_finiteRectShape]

/-- Exact original finite rectangular determinant/tableau identity. -/
theorem finiteCosineRectDet_eq_rectTableauSum (N m : ℕ) :
    finiteCosineRectDet N m = finiteRectTableauSum N m := by
  calc
    finiteCosineRectDet N m = finiteCosineAugDet N m 0 :=
      (finiteCosineAugDet_zero N m).symm
    _ = finiteAugTableauSum N m 0 :=
      finiteCosineAugDet_eq_augTableauSum N m 0 (Nat.zero_le m)
    _ = finiteRectTableauSum N m := by
      unfold finiteAugTableauSum
      rw [finiteAugShape_zero]
      simp [finiteRectTableauSum, finiteBottomWeight]

#assert_trust kernel finiteAugShape_zero
#assert_trust kernel finiteCosineRectDet_eq_rectTableauSum
#print axioms finiteCosineRectDet_eq_rectTableauSum

end NLA.Proofs.MF03
