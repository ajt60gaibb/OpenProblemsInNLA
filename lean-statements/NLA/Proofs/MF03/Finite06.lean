import NLA.Proofs.MF03.Disk
import Mathlib.Algebra.Polynomial.OfFn

/-! Exact rational MF-03 certificate for Padé order 6. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 2000000

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P06 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 7 ![
    (1 : ℂ),
    220574348151635/454605030049116,
    20837207639809/606140040065488,
    199961484798769/241849875986129712,
    38062401688454831/4440363723105341512320,
    116112688080827/2894459315802000393216,
    151259208063389819/2133505961677654489839513600]

private noncomputable def Q06 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 7 ![
    (1 : ℂ),
    -6728166872923/454605030049116,
    66817219029/606140040065488,
    -650617920073/1209249379930648560,
    8225608067111/4440363723105341512320,
    -2848116281867/651253346055450088473600,
    12170851069679/2133505961677654489839513600]

private theorem P06_degree : P06.natDegree ≤ 6 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 7) (![
    (1 : ℂ),
    220574348151635/454605030049116,
    20837207639809/606140040065488,
    199961484798769/241849875986129712,
    38062401688454831/4440363723105341512320,
    116112688080827/2894459315802000393216,
    151259208063389819/2133505961677654489839513600])
  dsimp only [P06]
  omega

private theorem Q06_degree : Q06.natDegree ≤ 6 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 7) (![
    (1 : ℂ),
    -6728166872923/454605030049116,
    66817219029/606140040065488,
    -650617920073/1209249379930648560,
    8225608067111/4440363723105341512320,
    -2848116281867/651253346055450088473600,
    12170851069679/2133505961677654489839513600])
  dsimp only [Q06]
  omega

private theorem Q06_coeff_zero : Q06.coeff 0 = 1 := by
  classical
  norm_num [Q06, Polynomial.ofFn_coeff_eq_val_of_lt]

/-- The exact rational pair satisfies every Padé equation through degree 12. -/
theorem finite06_normalized : NormalizedPadeRepresentation 6 P06 Q06 := by
  refine ⟨P06_degree, Q06_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q06_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P06, Q06, Finset.sum_range_succ,
        Polynomial.ofFn_coeff_eq_val_of_lt,
        Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- The explicit rational pair satisfies the full closed-disk estimate. -/
theorem finite06_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q06.eval z ≠ 0 ∧ ‖(1 : ℂ) - P06.eval z / Q06.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P06 Q06 6
    P06_degree Q06_degree Q06_coeff_zero
  · norm_num [Q06, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]
  · norm_num [P06, Q06, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]

#print axioms finite06_normalized
#assert_trust kernel finite06_normalized
#print axioms finite06_disk
#assert_trust kernel finite06_disk

end NLA.Proofs.MF03
