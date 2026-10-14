import NLA.Proofs.MF03.FiniteAugDetTableau
import NLA.Proofs.MF03.FiniteTableauTailBound

/-!
The original finite MF-03 augmented determinant obeys the exact
coefficient-one, `j`-fold original cosine-factor tail bound.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Exact finite determinant tail inequality with the original determinant,
rectangular tableau sum, and zero-based factor tail. -/
theorem finiteCosineAugDet_le_rect_mul_tail
    (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j ≤
      finiteRectTableauSum N m * (finiteCosineTail N m) ^ j := by
  rw [finiteCosineAugDet_eq_augTableauSum N m j hj]
  exact finiteAugTableauSum_le_rect_mul_tail N m j hj

#assert_trust kernel finiteCosineAugDet_le_rect_mul_tail
#print axioms finiteCosineAugDet_le_rect_mul_tail

end NLA.Proofs.MF03
