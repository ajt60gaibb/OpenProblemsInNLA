import NLA.Proofs.MF03.Disk
import Mathlib.Algebra.Polynomial.OfFn

/-! Exact rational MF-03 certificate for Padé order 7. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 2000000

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P07 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 8 ![
    (1 : ℂ),
    9494011832127130075/19482625349840916996,
    310367939726544641761/8767181407428412648200,
    290442017949426019417/322632275793365585453760,
    422064995289725174621/40651666749964063767173760,
    10143257867238927098753/169923967014849786546786316800,
    569672335133865317479319/3379787703925362254415579841152000,
    42948386132766526786783/227121733703784343496726965325414400]

private noncomputable def Q07 : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn 8 ![
    (1 : ℂ),
    -247300842793328423/19482625349840916996,
    711404045526343261/8767181407428412648200,
    -184363345338626039/537720459655609309089600,
    42648708634036181/40651666749964063767173760,
    -2008837845325770881/849619835074248932733931584000,
    1790291961275627717/482826814846480322059368548736000,
    -1651330565298296101/516185758417691689765288557557760000]

private theorem P07_degree : P07.natDegree ≤ 7 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 8) (![
    (1 : ℂ),
    9494011832127130075/19482625349840916996,
    310367939726544641761/8767181407428412648200,
    290442017949426019417/322632275793365585453760,
    422064995289725174621/40651666749964063767173760,
    10143257867238927098753/169923967014849786546786316800,
    569672335133865317479319/3379787703925362254415579841152000,
    42948386132766526786783/227121733703784343496726965325414400])
  dsimp only [P07]
  omega

private theorem Q07_degree : Q07.natDegree ≤ 7 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt
    (by norm_num : 1 ≤ 8) (![
    (1 : ℂ),
    -247300842793328423/19482625349840916996,
    711404045526343261/8767181407428412648200,
    -184363345338626039/537720459655609309089600,
    42648708634036181/40651666749964063767173760,
    -2008837845325770881/849619835074248932733931584000,
    1790291961275627717/482826814846480322059368548736000,
    -1651330565298296101/516185758417691689765288557557760000])
  dsimp only [Q07]
  omega

private theorem Q07_coeff_zero : Q07.coeff 0 = 1 := by
  classical
  norm_num [Q07, Polynomial.ofFn_coeff_eq_val_of_lt]

/-- The exact rational pair satisfies every Padé equation through degree 14. -/
theorem finite07_normalized : NormalizedPadeRepresentation 7 P07 Q07 := by
  refine ⟨P07_degree, Q07_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q07_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P07, Q07, Finset.sum_range_succ,
        Polynomial.ofFn_coeff_eq_val_of_lt,
        Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- The explicit rational pair satisfies the full closed-disk estimate. -/
theorem finite07_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q07.eval z ≠ 0 ∧ ‖(1 : ℂ) - P07.eval z / Q07.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P07 Q07 7
    P07_degree Q07_degree Q07_coeff_zero
  · norm_num [Q07, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]
  · norm_num [P07, Q07, Finset.sum_range_succ,
      Polynomial.ofFn_coeff_eq_val_of_lt]

#print axioms finite07_normalized
#assert_trust kernel finite07_normalized
#print axioms finite07_disk
#assert_trust kernel finite07_disk

end NLA.Proofs.MF03
