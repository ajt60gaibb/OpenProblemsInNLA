import NLA.Proofs.MF03.Disk
import Mathlib.Algebra.Polynomial.OfFn

/-! Exact rational MF-03 certificate for Padé order 3. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P₃ : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 4 ![(1 : ℂ), 3665/7788, 711/25960, 2923/7850304]

private noncomputable def Q₃ : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 4 ![(1 : ℂ), -229/7788, 1/2360, -127/39251520]

private theorem P₃_degree : P₃.natDegree ≤ 3 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 4) (![(1 : ℂ), 3665/7788, 711/25960, 2923/7850304])
  dsimp only [P₃]
  omega

private theorem Q₃_degree : Q₃.natDegree ≤ 3 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 4) (![(1 : ℂ), -229/7788, 1/2360, -127/39251520])
  dsimp only [Q₃]
  omega

private theorem Q₃_coeff_zero : Q₃.coeff 0 = 1 := by
  classical
  norm_num [Q₃, Polynomial.ofFn_coeff_eq_val_of_lt]

/-- The exact rational pair satisfies every Padé equation through degree 6. -/
theorem finite03_normalized : NormalizedPadeRepresentation 3 P₃ Q₃ := by
  refine ⟨P₃_degree, Q₃_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q₃_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P₃, Q₃, Finset.sum_range_succ,
        Polynomial.ofFn_coeff_eq_val_of_lt,
        Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- The explicit rational pair satisfies the full closed-disk estimate. -/
theorem finite03_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q₃.eval z ≠ 0 ∧ ‖(1 : ℂ) - P₃.eval z / Q₃.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P₃ Q₃ 3
    P₃_degree Q₃_degree Q₃_coeff_zero
  · norm_num [Q₃, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]
  · norm_num [P₃, Q₃, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]

#print axioms finite03_normalized
#assert_trust kernel finite03_normalized
#print axioms finite03_disk
#assert_trust kernel finite03_disk

end NLA.Proofs.MF03
