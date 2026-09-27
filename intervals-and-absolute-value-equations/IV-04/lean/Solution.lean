import Mathlib
import Reduction

namespace IV04

set_option autoImplicit false

theorem corner_solution_verified (M : TwoByTwo) (x₁ x₂ : ℚ)
    (hb : M.b = 1) (hdet : det M ≠ 0)
    (h₁ : M.a * x₁ + M.b * x₂ = 0)
    (h₂ : M.c * x₁ + M.d * x₂ = -1) :
    x₁ = 1 / det M :=
  corner_solution M x₁ x₂ hb hdet h₁ h₂

#print axioms corner_solution_verified

end IV04
