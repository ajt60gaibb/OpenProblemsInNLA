import NLA.Proofs.MF03.Disk
import Mathlib.Algebra.Polynomial.OfFn

/-! Exact rational MF-03 certificate for Padé order 4. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 2000000

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P04 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 5 ![
    (1 : ℂ),
    260735/545628,
    4375409/141863280,
    7696415/13108167072,
    80737373/23594700729600]

private noncomputable def Q04 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 5 ![
    (1 : ℂ),
    -12079/545628,
    34709/141863280,
    -109247/65540835360,
    11321/1814976979200]

private theorem P04_degree : P04.natDegree ≤ 4 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 5) (![
    (1 : ℂ),
    260735/545628,
    4375409/141863280,
    7696415/13108167072,
    80737373/23594700729600])
  dsimp only [P04]
  omega

private theorem Q04_degree : Q04.natDegree ≤ 4 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 5) (![
    (1 : ℂ),
    -12079/545628,
    34709/141863280,
    -109247/65540835360,
    11321/1814976979200])
  dsimp only [Q04]
  omega

private theorem Q04_coeff_zero : Q04.coeff 0 = 1 := by
  classical
  norm_num [Q04, Polynomial.ofFn_coeff_eq_val_of_lt]

/-- The exact rational pair satisfies every Padé equation through degree 8. -/
theorem finite04_normalized : NormalizedPadeRepresentation 4 P04 Q04 := by
  refine ⟨P04_degree, Q04_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q04_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P04, Q04, Finset.sum_range_succ,
        Polynomial.ofFn_coeff_eq_val_of_lt,
        Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- The explicit rational pair satisfies the full closed-disk estimate. -/
theorem finite04_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q04.eval z ≠ 0 ∧ ‖(1 : ℂ) - P04.eval z / Q04.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P04 Q04 4
    P04_degree Q04_degree Q04_coeff_zero
  · norm_num [Q04, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]
  · norm_num [P04, Q04, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]

#print axioms finite04_normalized
#assert_trust kernel finite04_normalized
#print axioms finite04_disk
#assert_trust kernel finite04_disk

end NLA.Proofs.MF03
