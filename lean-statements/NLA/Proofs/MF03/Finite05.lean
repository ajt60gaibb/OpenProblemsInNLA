import NLA.Proofs.MF03.Disk
import Mathlib.Algebra.Polynomial.OfFn

/-! Exact rational MF-03 certificate for Padé order 5. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 2000000

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P05 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 6 ![
    (1 : ℂ),
    5114526085/10605381164,
    53471234645/1622623318092,
    18894084119/25961973089472,
    2677576097699/425257119205551360,
    213692663231/11226787947026555904]

private noncomputable def Q05 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 6 ![
    (1 : ℂ),
    -188164497/10605381164,
    256513745/1622623318092,
    -117715523/129809865447360,
    1469628299/425257119205551360,
    -2045322787/280669698675663897600]

private theorem P05_degree : P05.natDegree ≤ 5 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 6) (![
    (1 : ℂ),
    5114526085/10605381164,
    53471234645/1622623318092,
    18894084119/25961973089472,
    2677576097699/425257119205551360,
    213692663231/11226787947026555904])
  dsimp only [P05]
  omega

private theorem Q05_degree : Q05.natDegree ≤ 5 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 6) (![
    (1 : ℂ),
    -188164497/10605381164,
    256513745/1622623318092,
    -117715523/129809865447360,
    1469628299/425257119205551360,
    -2045322787/280669698675663897600])
  dsimp only [Q05]
  omega

private theorem Q05_coeff_zero : Q05.coeff 0 = 1 := by
  classical
  norm_num [Q05, Polynomial.ofFn_coeff_eq_val_of_lt]

/-- The exact rational pair satisfies every Padé equation through degree 10. -/
theorem finite05_normalized : NormalizedPadeRepresentation 5 P05 Q05 := by
  refine ⟨P05_degree, Q05_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q05_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P05, Q05, Finset.sum_range_succ,
        Polynomial.ofFn_coeff_eq_val_of_lt,
        Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- The explicit rational pair satisfies the full closed-disk estimate. -/
theorem finite05_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q05.eval z ≠ 0 ∧ ‖(1 : ℂ) - P05.eval z / Q05.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P05 Q05 5
    P05_degree Q05_degree Q05_coeff_zero
  · norm_num [Q05, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]
  · norm_num [P05, Q05, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]

#print axioms finite05_normalized
#assert_trust kernel finite05_normalized
#print axioms finite05_disk
#assert_trust kernel finite05_disk

end NLA.Proofs.MF03
