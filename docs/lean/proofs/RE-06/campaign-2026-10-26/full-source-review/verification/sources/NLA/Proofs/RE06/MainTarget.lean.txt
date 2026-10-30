import NLA.Statements.RE06
import NLA.Proofs.RE06.FixedRepairProbability
import NLA.Proofs.RE06.GaussianSuccessAssembly
import NLA.Proofs.RE06.QueryBound

/-! The six public exports consume the unchanged reviewed operational model.
Every Gaussian rank, measurability and expectation obligation is discharged
internally. The exact-zero optimum and full-recovery branch are included. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.RE06
open NLA.Computation.NonadaptiveMatrixQuery

theorem successful (n m : ℕ) (hn : 0 < n)
    (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m) (hF : Function.Injective F)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.Successful F A ε := by
  have _ := hn
  have _ := hF
  by_cases hfull : n≤firstWidth m ε+secondWidth m ε+thirdWidth m ε
  · exact successful_full_branch F A ε hε0.le hfull
  apply successful_of_fixed_repair_estimate F A ε hε0 hεh
  intro B
  have hsketch := Nat.lt_of_not_ge hfull
  have hw := (Repair.actual_widths_strict m ε hε0).1
  have hr : rootWidth m≤n := by omega
  exact Repair.actual_fixed_repair_probability_budget B m ε hr hε0 hεh

theorem original_claim  :
    NLA.Statements.RE06.OriginalClaim := by
  refine ⟨4000000,by norm_num,0,?_⟩
  intro n m hn F hF A ε hε0 hεh
  exact ⟨query_bound n m hn ε hε0 hεh,successful n m hn F hF A ε hε0 hεh⟩

theorem explicit_claim  :
    NLA.Statements.RE06.ExplicitClaim := by
  intro n m hn F hF A ε hε0 hεh
  exact ⟨query_bound n m hn ε hε0 hεh,successful n m hn F hF A ε hε0 hεh⟩

theorem target  :
    NLA.Statements.RE06.Target :=
  ⟨svd_total,original_claim,explicit_claim⟩

#assert_trust kernel successful
#assert_trust kernel original_claim
#assert_trust kernel explicit_claim
#assert_trust kernel target
#print axioms successful
#print axioms original_claim
#print axioms explicit_claim
#print axioms target
end NLA.Proofs.RE06
