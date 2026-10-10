import NLA.Proofs.MF03.RectDeterminantPositivity
import NLA.Proofs.MF03.OriginalDeterminantInfiniteTail

/-!
The original infinite augmented determinant is nonnegative, and its
ratio to the positive original rectangular determinant obeys the exact
coefficient-one, `j`-fold cosine-factor tail bound.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter

namespace NLA.Proofs.MF03

/-- The original infinite augmented determinant is nonnegative as the
limit of positive original finite determinant/tableau sums. -/
theorem cosineAugDet_nonneg (m j : ℕ) (hj : j ≤ m) :
    0 ≤ cosineAugDet m j := by
  apply ge_of_tendsto (finiteCosineAugDet_tendsto m j hj)
  exact eventually_atTop.mpr
    ⟨m + 1, fun N hN => by
      rw [finiteCosineAugDet_eq_augTableauSum N m j hj]
      exact (finiteAugTableauSum_pos N m j hj (by omega)).le⟩

/-- The exact original determinant ratio is nonnegative and at most
the coefficient-one, `j`-fold tail, in every order. -/
theorem cosineAugDet_ratio_bounds (m j : ℕ) (hj : j ≤ m) :
    0 ≤ cosineAugDet m j / cosineRectDet m ∧
      cosineAugDet m j / cosineRectDet m ≤ (cosineTail m)^j := by
  constructor
  · exact div_nonneg (cosineAugDet_nonneg m j hj)
      (cosineRectDet_pos m).le
  · apply (div_le_iff₀ (cosineRectDet_pos m)).2
    simpa [mul_comm] using cosineAugDet_le_rectDet_mul_cosineTail m j hj

#assert_trust kernel cosineAugDet_nonneg
#assert_trust kernel cosineAugDet_ratio_bounds
#print axioms cosineAugDet_ratio_bounds

end NLA.Proofs.MF03
