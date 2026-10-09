import ProofProject.CStarSqrtSeparation

/-!
# Norm and separator bounds from the balanced factor identities

For a nonnormal operator the two absolute values remain distinct. Given
`X*X=|B|` and `YY*=|B*|`, all factor norm and separator bounds follow.
These estimates apply to factors satisfying the displayed identities.
-/

noncomputable section

namespace ProofProject

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma balancedFactor_norm_left {B X : A} (hX : star X * X = CFC.abs B) :
    ‖X‖ = Real.sqrt ‖B‖ := by
  calc
    ‖X‖ = Real.sqrt (‖X‖ * ‖X‖) := by rw [← sq, Real.sqrt_sq (norm_nonneg X)]
    _ = Real.sqrt ‖star X * X‖ := by rw [CStarRing.norm_star_mul_self]
    _ = _ := by rw [hX, CFC.norm_abs]

lemma balancedFactor_norm_right {B Y : A} (hY : Y * star Y = CFC.abs (star B)) :
    ‖Y‖ = Real.sqrt ‖B‖ := by
  calc
    ‖Y‖ = Real.sqrt (‖Y‖ * ‖Y‖) := by rw [← sq, Real.sqrt_sq (norm_nonneg Y)]
    _ = Real.sqrt ‖Y * star Y‖ := by rw [CStarRing.norm_self_mul_star]
    _ = _ := by rw [hY, CFC.norm_abs, norm_star]

/-- The right-factor separator estimate only uses the identity `YY*=|B*|`. -/
theorem balancedFactor_right_separator {B Y : A}
    (hY : Y * star Y = CFC.abs (star B)) (R : A) :
    ‖R * Y‖ ^ 2 ≤ ‖R‖ * ‖R * B‖ := by
  calc
    _ = ‖(R * Y) * star (R * Y)‖ := by rw [CStarRing.norm_self_mul_star, sq]
    _ = ‖R * CFC.abs (star B) * star R‖ := by
      rw [star_mul, mul_assoc R Y, ← mul_assoc Y, hY, ← mul_assoc]
    _ = ‖R * CFC.sqrt (CFC.abs (star B))‖ ^ 2 :=
      CFC.norm_mul_mul_star_self_of_nonneg R (CFC.abs_nonneg _)
    _ ≤ _ := norm_mul_sqrt_abs_star_sq_le R B

/-- The adjoint separator estimate uses the other absolute value. -/
theorem balancedFactor_left_separator {B X : A}
    (hX : star X * X = CFC.abs B) (R : A) :
    ‖star R * star X‖ ^ 2 ≤ ‖R‖ * ‖B * R‖ := by
  calc
    _ = ‖X * R‖ ^ 2 := by rw [← star_mul, norm_star]
    _ = ‖star (X * R) * (X * R)‖ := by rw [CStarRing.norm_star_mul_self, sq]
    _ = ‖star R * CFC.abs B * R‖ := by
      rw [star_mul, mul_assoc (star R) (star X), ← mul_assoc (star X), hX,
        ← mul_assoc]
    _ = ‖CFC.sqrt (CFC.abs B) * R‖ ^ 2 :=
      CFC.norm_star_mul_mul_self_of_nonneg R (CFC.abs_nonneg _)
    _ ≤ _ := norm_sqrt_abs_mul_sq_le B R

lemma sqrt_abs_balanced_left (B : A) :
    star (CFC.sqrt (CFC.abs B)) * CFC.sqrt (CFC.abs B) = CFC.abs B := by
  rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg B)]

end ProofProject
