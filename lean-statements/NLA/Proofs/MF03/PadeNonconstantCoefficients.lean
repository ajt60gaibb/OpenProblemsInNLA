import NLA.Proofs.MF03.CramerAugmentedDeterminant
import NLA.Proofs.MF03.OriginalDeterminantRatio

/-! Exact original determinant formula and coefficient-one tail bound for the
nonconstant all-order MF-03 Padé denominator coefficients. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix

namespace NLA.Proofs.MF03

/-- The nonconstant denominator coefficients, indexed by `c : Fin m` for
the coefficient of `z^(c.val+1)`, using the literal Cramer quotient. -/
noncomputable def cosinePadeNonconstantCoeff (m : ℕ) (c : Fin m) : ℝ :=
  (cosinePadeToeplitz m).cramer (cosinePadeRHS m) c /
    cosineRectDet m

/-- The exact high-degree Padé system, including the empty order-zero case. -/
theorem cosinePadeNonconstantCoeff_system (m : ℕ) :
    (cosinePadeToeplitz m) *ᵥ cosinePadeNonconstantCoeff m =
      cosinePadeRHS m := by
  have hdet : cosineRectDet m ≠ 0 := (cosineRectDet_pos m).ne'
  have hcoeff : cosinePadeNonconstantCoeff m =
      (cosineRectDet m)⁻¹ •
        (cosinePadeToeplitz m).cramer (cosinePadeRHS m) := by
    funext c
    simp [cosinePadeNonconstantCoeff, div_eq_mul_inv, mul_comm]
  rw [hcoeff, Matrix.mulVec_smul, cosinePadeToeplitz_mulVec_cramer]
  ext r
  simp [Pi.smul_apply, hdet]

/-- The exact manuscript sign and original infinite determinant ratio. -/
theorem cosinePadeNonconstantCoeff_eq_signed_ratio
    (m : ℕ) (c : Fin m) :
    cosinePadeNonconstantCoeff m c =
      (-1 : ℝ) ^ (c.val + 1) *
        (cosineAugDet m (c.val + 1) / cosineRectDet m) := by
  rw [cosinePadeNonconstantCoeff,
    cosinePadeToeplitz_cramer_eq_augDet]
  ring

/-- Every actual nonconstant denominator coefficient obeys the exact
coefficient-one cosine-factor tail bound. -/
theorem cosinePadeNonconstantCoeff_abs_le_tail
    (m : ℕ) (c : Fin m) :
    |cosinePadeNonconstantCoeff m c| ≤
      (cosineTail m) ^ (c.val + 1) := by
  have hj : c.val + 1 ≤ m := c.isLt
  have hb := cosineAugDet_ratio_bounds m (c.val + 1) hj
  rw [cosinePadeNonconstantCoeff_eq_signed_ratio]
  simpa [abs_mul, abs_pow, abs_of_nonneg hb.1] using hb.2

#assert_trust kernel cosinePadeNonconstantCoeff_system
#assert_trust kernel cosinePadeNonconstantCoeff_eq_signed_ratio
#assert_trust kernel cosinePadeNonconstantCoeff_abs_le_tail
#print axioms cosinePadeNonconstantCoeff_abs_le_tail

end NLA.Proofs.MF03
