import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Square-root separator bounds for nonnormal operators

The absolute values `CFC.abs B = sqrt(B*B)` and `CFC.abs (star B) = sqrt(BB*)`
are kept distinct. The C*-identity gives both separator estimates without a
normality hypothesis or a polar-decomposition assumption. The statements apply
in particular to bounded operators on any complete complex Hilbert space.
-/

noncomputable section

namespace ProofProject

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Left multiplication by `|B|` and by `B` have the same norm on every
right factor. This does not require `B` to be normal. -/
theorem norm_abs_mul_eq (B R : A) : ‖CFC.abs B * R‖ = ‖B * R‖ := by
  have hprod : star (CFC.abs B * R) * (CFC.abs B * R) =
      star (B * R) * (B * R) := by
    simp only [star_mul, (CFC.abs_nonneg B).star_eq]
    calc
      star R * CFC.abs B * (CFC.abs B * R) =
          star R * (CFC.abs B * CFC.abs B) * R := by simp only [mul_assoc]
      _ = star R * (star B * B) * R := by rw [CFC.abs_mul_abs]
      _ = star R * star B * (B * R) := by simp only [mul_assoc]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [CStarRing.norm_star_mul_self, ← sq] using congrArg norm hprod

/-- The corresponding right-multiplication identity uses `|B*|`, rather
than `|B|`. -/
theorem norm_mul_abs_star_eq (R B : A) :
    ‖R * CFC.abs (star B)‖ = ‖R * B‖ := by
  calc
    ‖R * CFC.abs (star B)‖ = ‖star (R * CFC.abs (star B))‖ :=
      (norm_star _).symm
    _ = ‖CFC.abs (star B) * star R‖ := by
      rw [star_mul, (CFC.abs_nonneg (star B)).star_eq]
    _ = ‖star B * star R‖ := norm_abs_mul_eq _ _
    _ = ‖R * B‖ := by rw [← star_mul, norm_star]

/-- The positive square-root sandwich estimate with the separator on the left. -/
theorem norm_mul_sqrt_sq_le (R P : A) (hP : 0 ≤ P) :
    ‖R * CFC.sqrt P‖ ^ 2 ≤ ‖R‖ * ‖R * P‖ := by
  calc
    ‖R * CFC.sqrt P‖ ^ 2 = ‖R * P * star R‖ :=
      (CFC.norm_mul_mul_star_self_of_nonneg R hP).symm
    _ ≤ ‖R * P‖ * ‖star R‖ := norm_mul_le _ _
    _ = ‖R‖ * ‖R * P‖ := by rw [norm_star, mul_comm]

/-- The positive square-root sandwich estimate with the separator on the right. -/
theorem norm_sqrt_mul_sq_le (P R : A) (hP : 0 ≤ P) :
    ‖CFC.sqrt P * R‖ ^ 2 ≤ ‖R‖ * ‖P * R‖ := by
  calc
    ‖CFC.sqrt P * R‖ ^ 2 = ‖star R * P * R‖ :=
      (CFC.norm_star_mul_mul_self_of_nonneg R hP).symm
    _ = ‖star R * (P * R)‖ := by rw [mul_assoc]
    _ ≤ ‖star R‖ * ‖P * R‖ := norm_mul_le _ _
    _ = ‖R‖ * ‖P * R‖ := by rw [norm_star]

/-- The `|B*|` separator bound required for the left positive factor. -/
theorem norm_mul_sqrt_abs_star_sq_le (R B : A) :
    ‖R * CFC.sqrt (CFC.abs (star B))‖ ^ 2 ≤ ‖R‖ * ‖R * B‖ := by
  simpa only [norm_mul_abs_star_eq] using
    norm_mul_sqrt_sq_le R (CFC.abs (star B)) (CFC.abs_nonneg _)

/-- The companion `|B|` separator bound. These two estimates use different
absolute values for a general nonnormal operator. -/
theorem norm_sqrt_abs_mul_sq_le (B R : A) :
    ‖CFC.sqrt (CFC.abs B) * R‖ ^ 2 ≤ ‖R‖ * ‖B * R‖ := by
  simpa only [norm_abs_mul_eq] using
    norm_sqrt_mul_sq_le (CFC.abs B) R (CFC.abs_nonneg _)

end ProofProject
