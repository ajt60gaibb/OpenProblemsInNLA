import NLA.Proofs.TR04.MachineTraceComposition

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04

structure ThresholdScanParameters where
  count : ℕ
  rank : ℕ
  base : ℕ

def thresholdAboveCount (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => tau < memory (P.base + i))).card

def thresholdTiedCount (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => memory (P.base + i) = tau)).card

def thresholdTakeCount (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => i < P.rank ∧ memory (P.base + i) = tau)).card

theorem thresholdAboveCount_zero (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) :
    thresholdAboveCount memory P tau 0 = 0 := by simp [thresholdAboveCount]

theorem thresholdTiedCount_zero (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) :
    thresholdTiedCount memory P tau 0 = 0 := by simp [thresholdTiedCount]

theorem thresholdTakeCount_zero (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) :
    thresholdTakeCount memory P tau 0 = 0 := by simp [thresholdTakeCount]

theorem thresholdAboveCount_succ (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) (k : ℕ) :
    thresholdAboveCount memory P tau (k + 1) = thresholdAboveCount memory P tau k +
      if tau < memory (P.base + k) then 1 else 0 := by
  classical
  by_cases h : tau < memory (P.base + k) <;>
    simp [thresholdAboveCount, Finset.range_add_one, Finset.filter_insert, h]

theorem thresholdTiedCount_succ (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) (k : ℕ) :
    thresholdTiedCount memory P tau (k + 1) = thresholdTiedCount memory P tau k +
      if memory (P.base + k) = tau then 1 else 0 := by
  classical
  by_cases h : memory (P.base + k) = tau <;>
    simp [thresholdTiedCount, Finset.range_add_one, Finset.filter_insert, h]

theorem thresholdTakeCount_succ (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau : ℝ) (k : ℕ) :
    thresholdTakeCount memory P tau (k + 1) = thresholdTakeCount memory P tau k +
      if k < P.rank ∧ memory (P.base + k) = tau then 1 else 0 := by
  classical
  by_cases h : k < P.rank ∧ memory (P.base + k) = tau <;>
    simp [thresholdTakeCount, Finset.range_add_one, Finset.filter_insert, h]

#assert_trust kernel thresholdAboveCount_succ
#assert_trust kernel thresholdTiedCount_succ
#assert_trust kernel thresholdTakeCount_succ
#print axioms thresholdTakeCount_succ
end NLA.Proofs.TR04
