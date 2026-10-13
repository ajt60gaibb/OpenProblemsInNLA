import NLA.Proofs.MF03.FiniteDeterminantLimit
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
The exact Toeplitz matrix and Cramer system for the original MF-03
all-order Padé equations. This algebra gate is conditional on the still-open
positivity of the rectangular determinant; it does not assert a normalized
Padé pair or the frozen Target.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix

namespace NLA.Proofs.MF03

/-- The exact real coefficient matrix for the nonconstant denominator
coefficients `q_(c+1)`, with row `r` representing degree `m+r+1`. -/
noncomputable def cosinePadeToeplitz (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun r c => cosineElementaryCoeff (m + r.val - c.val)

/-- The exact right-hand side of the high Padé equations. -/
noncomputable def cosinePadeRHS (m : ℕ) : Fin m → ℝ :=
  fun r => -cosineElementaryCoeff (m + r.val + 1)

/-- The Toeplitz determinant is the original rectangular determinant,
without a permutation sign or modified index. -/
theorem cosinePadeToeplitz_det (m : ℕ) :
    (cosinePadeToeplitz m).det = cosineRectDet m := by
  change (cosinePadeToeplitz m).det = ((cosinePadeToeplitz m)ᵀ).det
  exact (Matrix.det_transpose _).symm

/-- An unnormalized Cramer vector satisfies the exact high-degree system.
The determinant is retained as a scalar multiplier, with no division premise. -/
theorem cosinePadeToeplitz_mulVec_cramer (m : ℕ) :
    (cosinePadeToeplitz m) *ᵥ
        (cosinePadeToeplitz m).cramer (cosinePadeRHS m) =
      (cosineRectDet m) • (cosinePadeRHS m) := by
  rw [← cosinePadeToeplitz_det]
  exact Matrix.mulVec_cramer _ _

#assert_trust kernel cosinePadeToeplitz_det
#assert_trust kernel cosinePadeToeplitz_mulVec_cramer
#print axioms cosinePadeToeplitz_mulVec_cramer

end NLA.Proofs.MF03
