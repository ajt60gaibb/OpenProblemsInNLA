import NLA.Proofs.TR04.MachineBestCandidate

/-! Actual comparison and winner updates. Ties take the keep branch. All
three branches contain seven literal transitions, including padding jumps. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def bestCandidateResultScratch (p : BestCandidateData) (j : ℕ) (a b : ℝ) :
    BestCandidateScratch :=
  ⟨p.entries, p.entries, p.baseA + p.entries, p.candidateBase j + p.entries, 0,
    ![p.candidateError j, a, b]⟩

theorem bestCandidateProgram_first (p : BestCandidateData) (j winner : ℕ)
    (value a b : ℝ) (hj : j = 0) :
    (ordinaryStep bestCandidateProgram)^[7] (bestCandidateAfterError p j winner value a b) =
      bestCandidateLoopState p (j + 1) j (p.candidateError j)
        (bestCandidateResultScratch p j a b) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    bestCandidateProgram, bestCandidateAfterError, bestCandidateLoopState,
    bestCandidateState, bestCandidateResultScratch, hj, BestCandidateData.candidateBase]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem bestCandidateProgram_take (p : BestCandidateData) (j winner : ℕ)
    (value a b : ℝ) (hj : j ≠ 0) (hlt : p.candidateError j < value) :
    (ordinaryStep bestCandidateProgram)^[7] (bestCandidateAfterError p j winner value a b) =
      bestCandidateLoopState p (j + 1) j (p.candidateError j)
        (bestCandidateResultScratch p j a b) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    bestCandidateProgram, bestCandidateAfterError, bestCandidateLoopState,
    bestCandidateState, bestCandidateResultScratch, hj, hlt, BestCandidateData.candidateBase,
    Nat.add_mul, Nat.add_assoc]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem bestCandidateProgram_keep (p : BestCandidateData) (j winner : ℕ)
    (value a b : ℝ) (hj : j ≠ 0) (hlt : ¬ p.candidateError j < value) :
    (ordinaryStep bestCandidateProgram)^[7] (bestCandidateAfterError p j winner value a b) =
      bestCandidateLoopState p (j + 1) winner value
        (bestCandidateResultScratch p j a b) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    bestCandidateProgram, bestCandidateAfterError, bestCandidateLoopState,
    bestCandidateState, bestCandidateResultScratch, hj, hlt, BestCandidateData.candidateBase,
    Nat.add_mul, Nat.add_assoc]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

#assert_trust kernel bestCandidateProgram_first
#assert_trust kernel bestCandidateProgram_take
#assert_trust kernel bestCandidateProgram_keep
#print axioms bestCandidateProgram_first
#print axioms bestCandidateProgram_take
#print axioms bestCandidateProgram_keep
end NLA.Proofs.TR04
