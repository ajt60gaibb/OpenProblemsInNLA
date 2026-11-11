import NLA.Proofs.RE06.GaussianSelectedRepair

/-! Actual residual repair failure events and their finite-selected transport.
The uniform fixed-residual analytic estimate is an explicit internal premise;
it remains a separate mathematical proof obligation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- The literal residual error of the frozen two-sided SVD pseudoinverse repair. -/
def repairErrorFromEntries {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k ell : ℕ)
    (p : RepairEntries n k ell) : Matrix (Fin n) (Fin n) ℝ :=
  let G : Matrix (Fin n) (Fin k) ℝ := Matrix.of (fun i j => p.1 (i, j))
  let H : Matrix (Fin n) (Fin ell) ℝ := Matrix.of (fun i j => p.2 (i, j))
  let Y := B * G
  B - Y * pseudoInverse (H.transpose * Y) * (H.transpose * B)

def repairFailureSet {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k ell r : ℕ)
    (η : ℝ) : Set (RepairEntries n k ell) :=
  {p | (1 + η) * residualTailEnergy B r < squaredFrobenius (repairErrorFromEntries B k ell p) 0}

/-- Pointwise equality to the actual `sketchRepair`, before any probability argument. -/
theorem sketchRepair_error_from_entries {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n) (ω : ℕ → ℝ) :
    squaredFrobenius A (sketchRepair F A (makePlan n m ε ω)) =
      squaredFrobenius (repairErrorFromEntries
        (A - F (sketchWarmIndex F A (makePlan n m ε ω)))
        (secondWidth m ε) (thirdWidth m ε)
        (gaussianRepairEntries n (firstWidth m ε) (secondWidth m ε) (thirdWidth m ε) ω)) 0 := by
  rw [makePlan_sketch_blocks n m ε hsketch ω]
  rw [← squaredFrobenius_residual]
  apply congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => squaredFrobenius X 0)
  dsimp [sketchRepair, repairErrorFromEntries, gaussianRepairEntries]
  abel

/-- A proved uniform fixed-residual estimate transfers to the actual selected
repair under the original stream, without a factor `m+2`. -/
theorem actual_selected_repair_failure_le {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε η δ : ℝ)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n)
    (hfixed : ∀ B : Matrix (Fin n) (Fin n) ℝ,
      NullMeasurableSet (repairFailureSet B (secondWidth m ε) (thirdWidth m ε) (rootWidth m) η)
        (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)) ∧
      (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)).real
        (repairFailureSet B (secondWidth m ε) (thirdWidth m ε) (rootWidth m) η) ≤ δ) :
    NullMeasurableSet {ω | (1 + η) *
      residualTailEnergy (A - F (sketchWarmIndex F A (makePlan n m ε ω))) (rootWidth m) <
        squaredFrobenius A (sketchRepair F A (makePlan n m ε ω))} GaussianLaw ∧
    GaussianLaw.real {ω | (1 + η) *
      residualTailEnergy (A - F (sketchWarmIndex F A (makePlan n m ε ω))) (rootWidth m) <
        squaredFrobenius A (sketchRepair F A (makePlan n m ε ω))} ≤ δ := by
  have h := sketchWarmIndex_selected_failure_le F A ε hsketch
    (fun b => repairFailureSet (A - F b) (secondWidth m ε) (thirdWidth m ε) (rootWidth m) η)
    (fun b => (hfixed (A - F b)).1) δ (fun b => (hfixed (A - F b)).2)
  simpa only [repairFailureSet, Set.mem_ofPred_eq, ← sketchRepair_error_from_entries F A ε hsketch] using h

#assert_trust kernel repairErrorFromEntries
#assert_trust kernel repairFailureSet
#assert_trust kernel sketchRepair_error_from_entries
#assert_trust kernel actual_selected_repair_failure_le
#print axioms repairErrorFromEntries
#print axioms repairFailureSet
#print axioms sketchRepair_error_from_entries
#print axioms actual_selected_repair_failure_le
end NLA.Proofs.RE06
