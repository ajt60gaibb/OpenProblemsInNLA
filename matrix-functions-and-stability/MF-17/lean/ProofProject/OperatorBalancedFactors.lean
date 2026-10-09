import ProofProject.OperatorPolarExtension
import ProofProject.PolarFactorAlgebra

/-!
# Actual balanced factors for every bounded Hilbert-space operator

The range isometry supplies the polar operator. The resulting two factors
have the exact product, Gram identities, norms, and separator estimates for
general nonnormal operators, including operators with nonclosed range.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive left factor in the convention `B = Y X`. -/
def operatorLeftFactor (B : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (CFC.abs B)

/-- The right factor uses the actual polar extension. -/
def operatorRightFactor (B : H →L[ℂ] H) : H →L[ℂ] H :=
  operatorPolar B * operatorLeftFactor B

@[simp]
theorem operatorFactors_mul (B : H →L[ℂ] H) :
    operatorRightFactor B * operatorLeftFactor B = B := by
  simp only [operatorRightFactor, operatorLeftFactor, mul_assoc,
    CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg B), operatorPolar_mul_abs]

theorem operatorLeftFactor_gram (B : H →L[ℂ] H) :
    star (operatorLeftFactor B) * operatorLeftFactor B = CFC.abs B :=
  sqrt_abs_balanced_left B

theorem operatorRightFactor_gram (B : H →L[ℂ] H) :
    operatorRightFactor B * star (operatorRightFactor B) = CFC.abs (star B) :=
  polarFactor_right_gram (operatorPolar_mul_abs B) (operatorPolar_support_abs B)

@[simp]
theorem norm_operatorLeftFactor (B : H →L[ℂ] H) :
    ‖operatorLeftFactor B‖ = Real.sqrt ‖B‖ :=
  balancedFactor_norm_left (operatorLeftFactor_gram B)

@[simp]
theorem norm_operatorRightFactor (B : H →L[ℂ] H) :
    ‖operatorRightFactor B‖ = Real.sqrt ‖B‖ :=
  balancedFactor_norm_right (operatorRightFactor_gram B)

theorem operatorRightFactor_separator (B R : H →L[ℂ] H) :
    ‖R * operatorRightFactor B‖ ^ 2 ≤ ‖R‖ * ‖R * B‖ :=
  balancedFactor_right_separator (operatorRightFactor_gram B) R

theorem operatorLeftFactor_adjoint_separator (B R : H →L[ℂ] H) :
    ‖star R * star (operatorLeftFactor B)‖ ^ 2 ≤ ‖R‖ * ‖B * R‖ :=
  balancedFactor_left_separator (operatorLeftFactor_gram B) R

end ProofProject
