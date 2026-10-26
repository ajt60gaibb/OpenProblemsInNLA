import NLA.Proofs.TR04.MachineThresholdScan

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

set_option maxHeartbeats 1600000 in
theorem thresholdScanProgram_nine_steps (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (k : ℕ) (hk : k < P.count) :
    (ordinaryStep thresholdScanProgram)^[9] (thresholdScanLoopState memory P tau k scratch) =
      thresholdScanLoopState memory P tau (k + 1) (memory (P.base + k)) := by
  by_cases hg : tau < memory (P.base + k)
  · have he : memory (P.base + k) ≠ tau := ne_of_gt hg
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      thresholdScanProgram, thresholdScanLoopState, hk, hg, he,
      thresholdAboveCount_succ, thresholdTiedCount_succ, thresholdTakeCount_succ, Nat.add_assoc]
    all_goals try rfl
    all_goals funext r
    all_goals fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · by_cases he : memory (P.base + k) = tau
    · by_cases hr : k < P.rank
      all_goals apply machineState_ext
      all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
        thresholdScanProgram, thresholdScanLoopState, hk, he, hr,
        thresholdAboveCount_succ, thresholdTiedCount_succ, thresholdTakeCount_succ, Nat.add_assoc]
      all_goals try rfl
      all_goals funext r
      all_goals fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff]
    · apply machineState_ext
      all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
        thresholdScanProgram, thresholdScanLoopState, hk, hg, he,
        thresholdAboveCount_succ, thresholdTiedCount_succ, thresholdTakeCount_succ, Nat.add_assoc]
      all_goals try rfl
      all_goals funext r
      all_goals fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem thresholdScanProgram_iterations (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (k : ℕ) (hk : k ≤ P.count) :
    ∃ v : ℝ, (ordinaryStep thresholdScanProgram)^[9 * k]
      (thresholdScanLoopState memory P tau 0 scratch) = thresholdScanLoopState memory P tau k v := by
  induction k with
  | zero => exact ⟨scratch, rfl⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih (by omega)
    refine ⟨memory (P.base + k), ?_⟩
    rw [Nat.mul_succ, Nat.add_comm (9 * k) 9, Function.iterate_add_apply, hv]
    exact thresholdScanProgram_nine_steps memory P tau v k (by omega)

#assert_trust kernel thresholdScanProgram_nine_steps
#assert_trust kernel thresholdScanProgram_iterations
#print axioms thresholdScanProgram_iterations
end NLA.Proofs.TR04
