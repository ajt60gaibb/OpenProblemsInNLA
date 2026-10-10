import NLA.Proofs.MF03.FiniteRectDetTableau
import NLA.Proofs.MF03.FiniteTableauInfiniteTail

/-!
The exact coefficient-one cosine-factor tail inequality for the
original finite and infinite MF-03 determinants.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter

namespace NLA.Proofs.MF03

/-- The original finite augmented determinant is bounded by the original
finite rectangular determinant and the infinite `j`-fold factor tail. -/
theorem finiteCosineAugDet_le_rectDet_mul_cosineTail
    (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j ≤
      finiteCosineRectDet N m * (cosineTail m)^j := by
  rw [finiteCosineAugDet_eq_augTableauSum N m j hj,
    finiteCosineRectDet_eq_rectTableauSum N m]
  exact finiteAugTableauSum_le_rect_mul_cosineTail N m j hj

/-- The same coefficient-one inequality holds for the original infinite
elementary-coefficient determinants by fixed-size determinant limits. -/
theorem cosineAugDet_le_rectDet_mul_cosineTail
    (m j : ℕ) (hj : j ≤ m) :
    cosineAugDet m j ≤ cosineRectDet m * (cosineTail m)^j := by
  apply le_of_tendsto_of_tendsto'
    (finiteCosineAugDet_tendsto m j hj)
    ((finiteCosineRectDet_tendsto m).mul tendsto_const_nhds)
  intro N
  exact finiteCosineAugDet_le_rectDet_mul_cosineTail N m j hj

#assert_trust kernel finiteCosineAugDet_le_rectDet_mul_cosineTail
#assert_trust kernel cosineAugDet_le_rectDet_mul_cosineTail
#print axioms cosineAugDet_le_rectDet_mul_cosineTail

end NLA.Proofs.MF03
