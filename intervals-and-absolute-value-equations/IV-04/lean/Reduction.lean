import Mathlib

namespace IV04

structure TwoByTwo where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def det (M : TwoByTwo) : ℝ := M.a * M.d - M.b * M.c

lemma corner_solution (M : TwoByTwo) (x₁ x₂ : ℝ)
    (hb : M.b = 1) (hdet : det M ≠ 0)
    (h₁ : M.a * x₁ + M.b * x₂ = 0)
    (h₂ : M.c * x₁ + M.d * x₂ = -1) :
    x₁ = 1 / det M := by
  dsimp [det] at hdet ⊢
  rw [hb] at hdet h₁ ⊢
  have hdetx : (M.a * M.d - M.c) * x₁ = 1 := by
    linear_combination M.d * h₁ - h₂
  apply (eq_div_iff hdet).2
  nlinarith [hdetx]

end IV04
