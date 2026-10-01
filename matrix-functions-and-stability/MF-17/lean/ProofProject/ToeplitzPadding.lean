import ProofProject.FiniteToeplitz

/-!
# Removing the first zero row of a shifted Toeplitz operator

Multiplication of the symbol by `X` shifts its coefficients by one. Appending
a zero to the input then gives a zero followed by the unshifted output. Both
padding operations preserve Euclidean squared energy, also in dimension zero.
-/

noncomputable section

namespace ProofProject

open Polynomial

variable {m : ℕ}

/-- The exact shifted action, with appended input zero and leading output zero. -/
theorem finiteToeplitzApply_X_mul_snoc (S : Polynomial ℂ) (u : Fin m → ℂ) :
    finiteToeplitzApply (X * S).coeff (Fin.snoc u 0) =
      Fin.cons 0 (finiteToeplitzApply S.coeff u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [finiteToeplitzApply]
  · rw [Fin.cons_succ]
    unfold finiteToeplitzApply
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_succ,
      mul_zero, ite_self, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j.val ≤ i.val
    · rw [if_pos (Nat.le_succ_of_le hji), if_pos hji]
      rw [show i.val + 1 - j.val = (i.val - j.val) + 1 by omega, coeff_X_mul]
    · rw [if_neg hji]
      split_ifs with hji'
      · rw [show i.val + 1 - j.val = 0 by omega, coeff_X_mul_zero, zero_mul]
      · rfl

lemma toeplitz_snoc_zero_energy (u : Fin m → ℂ) :
    (∑ i : Fin (m + 1), ‖Fin.snoc (α := fun _ => ℂ) u 0 i‖ ^ 2) =
      ∑ i : Fin m, ‖u i‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp

lemma toeplitz_cons_zero_energy (u : Fin m → ℂ) :
    (∑ i : Fin (m + 1), ‖Fin.cons (α := fun _ => ℂ) 0 u i‖ ^ 2) =
      ∑ i : Fin m, ‖u i‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp

/-- The padding argument preserves the bound itself; in particular it passes
a contraction bound from `X*S` in dimension `m+1` to `S` in dimension `m`. -/
theorem HasFiniteToeplitzBound.of_X_mul {S : Polynomial ℂ} {ρ : ℝ}
    (h : HasFiniteToeplitzBound (X * S).coeff (m + 1) ρ) :
    HasFiniteToeplitzBound S.coeff m ρ := by
  intro u
  have hu := h (Fin.snoc u 0)
  rw [finiteToeplitzApply_X_mul_snoc, toeplitz_cons_zero_energy,
    toeplitz_snoc_zero_energy] at hu
  exact hu

end ProofProject
