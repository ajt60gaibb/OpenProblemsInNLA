import ProofProject.BalancedOperatorFactors

/-!
# Balanced factors from the two polar support identities

Only `U |B| = B` and `U* U |B| = |B|` are needed. Positivity and uniqueness
of the square root give the other Gram identity without a square-root
intertwining formula.
-/

noncomputable section

namespace ProofProject

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem polarFactor_right_gram {B U : A}
    (hUB : U * CFC.abs B = B)
    (hsupport : star U * U * CFC.abs B = CFC.abs B) :
    (U * CFC.sqrt (CFC.abs B)) * star (U * CFC.sqrt (CFC.abs B)) =
      CFC.abs (star B) := by
  let Y := U * CFC.sqrt (CFC.abs B)
  have hY : Y * star Y = U * CFC.abs B * star U := by
    dsimp only [Y]
    rw [star_mul, (CFC.sqrt_nonneg _).star_eq,
      mul_assoc U, ← mul_assoc (CFC.sqrt (CFC.abs B)),
      CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg B), ← mul_assoc]
  have hsquare : (Y * star Y) * (Y * star Y) = B * star B := by
    rw [hY]
    calc
      _ = U * CFC.abs B * (star U * U * CFC.abs B) * star U := by
        simp only [mul_assoc]
      _ = U * CFC.abs B * CFC.abs B * star U := by rw [hsupport]
      _ = (U * CFC.abs B) * star (U * CFC.abs B) := by
        rw [star_mul, (CFC.abs_nonneg B).star_eq]
        simp only [mul_assoc]
      _ = _ := by rw [hUB]
  have hroot := CFC.sqrt_unique hsquare (mul_star_self_nonneg Y)
  change Y * star Y = CFC.abs (star B)
  simpa only [CFC.abs, star_star] using hroot.symm

/-- Conditional on the actual polar support identities, the factors exist
with exactly the two Gram identities used by the separator estimates. -/
theorem exists_balancedFactors_of_polarSupport {B U : A}
    (hUB : U * CFC.abs B = B)
    (hsupport : star U * U * CFC.abs B = CFC.abs B) :
    ∃ X Y : A, Y * X = B ∧ star X * X = CFC.abs B ∧
      Y * star Y = CFC.abs (star B) := by
  refine ⟨CFC.sqrt (CFC.abs B), U * CFC.sqrt (CFC.abs B), ?_,
    sqrt_abs_balanced_left B, polarFactor_right_gram hUB hsupport⟩
  rw [mul_assoc, CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg B), hUB]

end ProofProject
