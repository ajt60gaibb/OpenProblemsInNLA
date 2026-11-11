import NLA.Proofs.RE06.GaussianMomentOuter
import NLA.Proofs.RE06.GaussianRepairBudget
import NLA.Proofs.RE06.RepairMarkov

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem fixed_repair_probability {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r≤n)
    (hk : r+1<k) (hell : k+1<ell) (η : ℝ) (hη : 0<η) :
    NullMeasurableSet (repairFailureSet C k ell r η) (gaussianRepairLaw n k ell) ∧
      (gaussianRepairLaw n k ell).real (repairFailureSet C k ell r η) ≤
        (((r:ℝ)/((k:ℝ)-(r:ℝ)-1)) + ((k:ℝ)/((ell:ℝ)-(k:ℝ)-1)) +
          ((r:ℝ)/((k:ℝ)-(r:ℝ)-1))*((k:ℝ)/((ell:ℝ)-(k:ℝ)-1)))/η := by
  letI : IsProbabilityMeasure (gaussianRepairLaw n k ell) := by
    unfold gaussianRepairLaw
    infer_instance
  let a := (r:ℝ)/((k:ℝ)-(r:ℝ)-1)
  let b := (k:ℝ)/((ell:ℝ)-(k:ℝ)-1)
  have hkr : (r:ℝ)+1<(k:ℝ) := by exact_mod_cast hk
  have helr : (k:ℝ)+1<(ell:ℝ) := by exact_mod_cast hell
  have ha : 0≤a := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hb : 0≤b := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have htail : 0≤residualTailEnergy C r := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := GaussianMoment.actual_excess_majorant_moment C r hr hk hell
  have hprob := nonnegative_majorant_tail_bound (gaussianRepairLaw n k ell)
    (fun x => squaredFrobenius (repairErrorFromEntries C k ell x) 0)
    (fun x => actualExcessMajorant C r hr
      (Matrix.of (fun i j => x.1 (i,j))) (Matrix.of (fun i j => x.2 (i,j))).transpose)
    (residualTailEnergy C r) η (a+b+a*b) htail hη
    (add_nonneg (add_nonneg ha hb) (mul_nonneg ha hb))
    (fun _ => actualExcessMajorant_nonneg _ _ _ _ _) hm.1
    (GaussianMoment.gaussianRepair_majorant_ae C r hr (by omega)) hm.2
  exact ⟨nullMeasurableSet_repairFailureSet C k ell r η,hprob⟩

theorem actual_fixed_repair_probability_budget {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (ε : ℝ) (hr : rootWidth m≤n)
    (hε0 : 0<ε) (hεh : ε<1/2) :
    NullMeasurableSet
      (repairFailureSet C (secondWidth m ε) (thirdWidth m ε) (rootWidth m) (ε/4))
      (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)) ∧
      (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)).real
        (repairFailureSet C (secondWidth m ε) (thirdWidth m ε) (rootWidth m) (ε/4)) ≤
          (1/128:ℝ)+1/524288 := by
  have hw := actual_widths_strict m ε hε0
  have hrati := actual_width_ratios m ε hε0
  have hp := fixed_repair_probability C (rootWidth m) hr hw.1 hw.2 (ε/4) (by positivity)
  refine ⟨hp.1,hp.2.trans ?_⟩
  exact repair_failure_ratio_bound _ _ (ε/4) (by positivity) (by linarith)
    hrati.1 hrati.2.2.1 hrati.2.1 hrati.2.2.2

#assert_trust kernel fixed_repair_probability
#assert_trust kernel actual_fixed_repair_probability_budget
#print axioms actual_fixed_repair_probability_budget
end NLA.Proofs.RE06.Repair
