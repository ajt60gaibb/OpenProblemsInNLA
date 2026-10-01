import Mathlib

/-! A positive circle phase for the finite polynomial factorization argument. -/

noncomputable section

namespace ProofProject

/-- On the unit circle, a polynomial has phase `z^m` and a strictly positive
real amplitude. This is the polynomial form of a positive trigonometric weight. -/
def HasPositiveCirclePhase (m : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∃ r : ℝ, 0 < r ∧ p.eval z = z ^ m * (r : ℂ)

end ProofProject
