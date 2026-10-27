import NLA.Proofs.RE05.RegressionOffset

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

def coefficientVector {m : ℕ} (c : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 c

theorem coefficientVector_inner {m : ℕ} (c d : Fin m → ℝ) :
    dot c d = ⟪coefficientVector c, coefficientVector d⟫_ℝ := by
  simp [coefficientVector, EuclideanSpace.inner_eq_star_dotProduct, dot, dotProduct, mul_comm]

theorem coefficientVector_norm_sq {m : ℕ} (c : Fin m → ℝ) :
    dot c c = ‖coefficientVector c‖ ^ 2 := by
  rw [coefficientVector_inner, real_inner_self_eq_norm_sq]

/-- Euclidean Cauchy--Schwarz and a positive quadratic lower bound give the
coefficient error estimate. No division by an optimum or residual occurs. -/
theorem coefficient_error_bound {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ)
    (α : ℝ) (hα : 0 < α) (hLower : ∀ d : Fin m → ℝ, α * dot d d ≤ dot d (G *ᵥ d))
    (d z : Fin m → ℝ) (heq : G *ᵥ d = z) :
    dot d d ≤ (1 / α ^ 2) * dot z z := by
  have hCS := real_inner_le_norm (coefficientVector d) (coefficientVector z)
  rw [← coefficientVector_inner] at hCS
  have hl := hLower d
  rw [heq, coefficientVector_norm_sq] at hl
  have hdz : α * ‖coefficientVector d‖ ^ 2 ≤
      ‖coefficientVector d‖ * ‖coefficientVector z‖ := hl.trans hCS
  have hnorm : α * ‖coefficientVector d‖ ≤ ‖coefficientVector z‖ := by
    by_cases hd : ‖coefficientVector d‖ = 0
    · simpa only [hd, mul_zero] using norm_nonneg (coefficientVector z)
    · have hp : 0 < ‖coefficientVector d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [hdz]
  have hs := (sq_le_sq₀ (mul_nonneg hα.le (norm_nonneg _)) (norm_nonneg _)).mpr hnorm
  rw [coefficientVector_norm_sq, coefficientVector_norm_sq, one_div,
    ← div_eq_inv_mul]
  apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
  calc
    ‖coefficientVector d‖ ^ 2 * α ^ 2 = (α * ‖coefficientVector d‖) ^ 2 := by ring
    _ ≤ _ := hs

theorem singleOutput_coefficient_error {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (A : Square n) (c : Fin (q + 1) → ℝ) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ d : Fin (q + 1) → ℝ, α * dot d d ≤ dot d (gram P plan *ᵥ d)) :
    dot (singleOutput P plan (planAnswers A plan) - c)
      (singleOutput P plan (planAnswers A plan) - c) ≤
      (1 / α ^ 2) * dot (regressionOffset P plan (A - represent P c))
        (regressionOffset P plan (A - represent P c)) :=
  coefficient_error_bound (gram P plan) α hα hLower _ _
    (singleOutput_residual_equation P plan A c)

end NLA.Proofs.RE05
