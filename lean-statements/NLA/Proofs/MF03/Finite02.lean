import NLA.Proofs.MF03.Disk
import Mathlib.Algebra.Polynomial.OfFn

/-! Exact rational MF-03 certificate for Padé order two. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P₂ : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 3 ![(1 : ℂ), 115 / 252, 313 / 15120]

private noncomputable def Q₂ : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 3 ![(1 : ℂ), -(11 / 252), 13 / 15120]

private theorem P₂_degree : P₂.natDegree ≤ 2 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 3)
    (![(1 : ℂ), 115 / 252, 313 / 15120])
  dsimp only [P₂]
  omega

private theorem Q₂_degree : Q₂.natDegree ≤ 2 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 3)
    (![(1 : ℂ), -(11 / 252), 13 / 15120])
  dsimp only [Q₂]
  omega

private theorem Q₂_coeff_zero : Q₂.coeff 0 = 1 := by
  classical
  norm_num [Q₂, Polynomial.ofFn_coeff_eq_val_of_lt]

/-- The exact rational pair satisfies every Padé equation through degree 4. -/
theorem order_two_normalized : NormalizedPadeRepresentation 2 P₂ Q₂ := by
  refine ⟨P₂_degree, Q₂_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q₂_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P₂, Q₂, Finset.sum_range_succ,
        Polynomial.ofFn_coeff_eq_val_of_lt,
        Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- The order-two rational pair satisfies the full closed-disk estimate. -/
theorem order_two_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q₂.eval z ≠ 0 ∧ ‖(1 : ℂ) - P₂.eval z / Q₂.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P₂ Q₂ 2 P₂_degree Q₂_degree Q₂_coeff_zero
  · norm_num [Q₂, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]
  · norm_num [P₂, Q₂, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]

#print axioms order_two_normalized
#assert_trust kernel order_two_normalized
#print axioms order_two_disk
#assert_trust kernel order_two_disk

end NLA.Proofs.MF03
