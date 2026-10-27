import NLA.Proofs.RE06.GaussianRepairSelectionActual
import NLA.Proofs.RE06.GaussianWarmBudget
import NLA.Proofs.RE06.Frobenius

/-! Internal success assembly for the actual frozen algorithm. The true uniform
fixed-residual repair estimate remains an explicit mathematical premise here;
this file does not define any frozen public success export. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- The two square-error estimates give the required repair norm, including
zero optimum, without division by the optimum. -/
theorem repair_norm_of_tail_bounds {a b : ℕ}
    (X Y : Matrix (Fin a) (Fin b) ℝ) (O tail η : ℝ)
    (hO : 0 ≤ O) (hη0 : 0 ≤ η) (hηh : η ≤ 1 / 8)
    (hTail : tail ≤ ((1 + η) / (1 - η)) * O ^ 2)
    (hRepair : squaredFrobenius X Y ≤ (1 + η) * tail) :
    frobenius X Y ≤ (1 + 2 * η) * O := by
  have hden : 0 < 1 - η := by linarith
  have hηsq : η ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by nlinarith
  have hgap : (1 + η) * ((1 + η) / (1 - η)) ≤ (1 + 2 * η) ^ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    have hp : 0 ≤ η * (1 - η - 4 * η ^ 2) :=
      mul_nonneg hη0 (by nlinarith)
    nlinarith
  have hs : squaredFrobenius X Y ≤ ((1 + 2 * η) * O) ^ 2 := by
    calc
      _ ≤ (1 + η) * (((1 + η) / (1 - η)) * O ^ 2) :=
        hRepair.trans (mul_le_mul_of_nonneg_left hTail (by linarith))
      _ = ((1 + η) * ((1 + η) / (1 - η))) * O ^ 2 := by ring
      _ ≤ (1 + 2 * η) ^ 2 * O ^ 2 := mul_le_mul_of_nonneg_right hgap (sq_nonneg O)
      _ = _ := by ring
  unfold NLA.Computation.NonadaptiveMatrixQuery.frobenius
  calc
    _ ≤ Real.sqrt (((1 + 2 * η) * O) ^ 2) := Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_sq (mul_nonneg (by linarith) hO)

/-- Internal probability assembly. Its only unproved analytic ingredient is
exactly the actual fixed-residual repair event estimate in `hfixed`. -/
theorem successful_of_fixed_repair_estimate {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2)
    (hfixed : ∀ B : Matrix (Fin n) (Fin n) ℝ,
      NullMeasurableSet
        (repairFailureSet B (secondWidth m ε) (thirdWidth m ε) (rootWidth m) (ε / 4))
        (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)) ∧
      (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)).real
        (repairFailureSet B (secondWidth m ε) (thirdWidth m ε) (rootWidth m) (ε / 4)) ≤
          (1 / 128 : ℝ) + 1 / 524288) :
    Successful F A ε := by
  classical
  by_cases hfull : n ≤ firstWidth m ε + secondWidth m ε + thirdWidth m ε
  · exact successful_full_branch F A ε hε0.le hfull
  have hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n :=
    Nat.lt_of_not_ge hfull
  let K (ω : ℕ → ℝ) := sketchWarmIndex F A (makePlan n m ε ω)
  let tail (ω : ℕ → ℝ) := residualTailEnergy (A - F (K ω)) (rootWidth m)
  let badWarm : Set (ℕ → ℝ) :=
    {ω | ((1 + ε / 4) / (1 - ε / 4)) * (optimum A F) ^ 2 < tail ω}
  let badRepair : Set (ℕ → ℝ) :=
    {ω | (1 + ε / 4) * tail ω < squaredFrobenius A (sketchRepair F A (makePlan n m ε ω))}
  have htailmeas : Measurable tail :=
    measurable_score_at_finite_index
      (fun b (_ : ℕ → ℝ) => residualTailEnergy (A - F b) (rootWidth m))
      (fun _ => measurable_const) K (sketchWarmIndex_measurable F A ε)
  have hWarmMeas : MeasurableSet badWarm := measurableSet_lt measurable_const htailmeas
  have hWarm : GaussianLaw.real badWarm ≤ 2 * Real.exp (-16) + Real.exp (-8) :=
    sketchWarmIndex_explicit_tail_bound F A ε hε0 hεh hsketch
  have hRepair := actual_selected_repair_failure_le F A ε (ε / 4)
    ((1 / 128 : ℝ) + 1 / 524288) hsketch hfixed
  have hRepairMeas : NullMeasurableSet badRepair GaussianLaw := hRepair.1
  have hRepairProb : GaussianLaw.real badRepair ≤ (1 / 128 : ℝ) + 1 / 524288 := hRepair.2
  have hUnionMeas : NullMeasurableSet (badWarm ∪ badRepair) GaussianLaw :=
    hWarmMeas.nullMeasurableSet.union hRepairMeas
  have hUnionProb : GaussianLaw.real (badWarm ∪ badRepair) < 1 / 100 := by
    have hu := measureReal_union_le (μ := GaussianLaw) badWarm badRepair
    have hn := gaussian_total_failure_budget_lt
    linarith
  have hGoodProb : (99 / 100 : ℝ) ≤ GaussianLaw.real (badWarm ∪ badRepair)ᶜ := by
    rw [probReal_compl_eq_one_sub₀ hUnionMeas]
    linarith
  have hGoodSubset : (badWarm ∪ badRepair)ᶜ ⊆
      {ω | frobenius A (run F A ε ω) ≤ (3 + ε) * optimum A F} := by
    intro ω hω
    have hw : tail ω ≤ ((1 + ε / 4) / (1 - ε / 4)) * (optimum A F) ^ 2 := by
      have hnot : ω ∉ badWarm := fun h => hω (Or.inl h)
      exact le_of_not_gt hnot
    have hr : squaredFrobenius A (sketchRepair F A (makePlan n m ε ω)) ≤
        (1 + ε / 4) * tail ω := by
      have hnot : ω ∉ badRepair := fun h => hω (Or.inr h)
      exact le_of_not_gt hnot
    have hnorm := repair_norm_of_tail_bounds A (sketchRepair F A (makePlan n m ε ω))
      (optimum A F) (tail ω) (ε / 4) (frobenius_nonnegative _ _)
      (by positivity) (by linarith) hw hr
    have hp : (makePlan n m ε ω).full = false := by simp [makePlan, hfull]
    have hrun := run_sketch_error_of_repair F A ε (ε / 4) ω hp hnorm
    change frobenius A (run F A ε ω) ≤ (3 + ε) * optimum A F
    convert hrun using 1 <;> ring
  unfold Successful
  apply le_trans ?_ (measure_mono hGoodSubset)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, measureReal_def] using hGoodProb

#assert_trust kernel repair_norm_of_tail_bounds
#assert_trust kernel successful_of_fixed_repair_estimate
#print axioms repair_norm_of_tail_bounds
#print axioms successful_of_fixed_repair_estimate
end NLA.Proofs.RE06
