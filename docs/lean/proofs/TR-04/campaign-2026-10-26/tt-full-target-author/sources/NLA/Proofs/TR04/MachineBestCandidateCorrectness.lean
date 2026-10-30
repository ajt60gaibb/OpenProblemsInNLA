import NLA.Proofs.TR04.MachineBestCandidateBranches
import NLA.Proofs.TR04.MachineBestCandidateError

/-! The actual selector returns an actual least-error candidate. The winner
invariant is derived from literal comparisons, and all memory is read-only. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def bestCandidateIterationTime (p : BestCandidateData) : ℕ := 9 * p.entries + 15
def bestCandidateTime (p : BestCandidateData) : ℕ :=
  bestCandidateIterationTime p * p.count + 4

def bestCandidateStart (p : BestCandidateData) (value : ℝ) (scratch : BestCandidateScratch) :
    State bestCandidateProgram := { bestCandidateLoopState p 0 0 value scratch with label := 0 }

theorem bestCandidateProgram_initial (p : BestCandidateData) (value : ℝ)
    (scratch : BestCandidateScratch) :
    (ordinaryStep bestCandidateProgram)^[2] (bestCandidateStart p value scratch) =
      bestCandidateLoopState p 0 0 value scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    bestCandidateProgram, bestCandidateStart, bestCandidateLoopState,
    bestCandidateState, BestCandidateData.candidateBase]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem bestCandidateProgram_iteration (p : BestCandidateData) (j winner : ℕ)
    (value : ℝ) (scratch : BestCandidateScratch) (hj : j < p.count)
    (hmin : p.MinimumSoFar j winner value) :
    ∃ winner' : ℕ, ∃ value' : ℝ, ∃ result : BestCandidateScratch,
      (ordinaryStep bestCandidateProgram)^[bestCandidateIterationTime p]
        (bestCandidateLoopState p j winner value scratch) =
          bestCandidateLoopState p (j + 1) winner' value' result ∧
      p.MinimumSoFar (j + 1) winner' value' := by
  obtain ⟨a, b, he⟩ := bestCandidateProgram_error p j winner value scratch.real
  have ht : bestCandidateIterationTime p = 7 + ((9 * p.entries + 2) + 6) := by
    unfold bestCandidateIterationTime
    omega
  by_cases hz : j = 0
  · refine ⟨j, p.candidateError j, bestCandidateResultScratch p j a b, ?_,
      p.minimum_take j winner value hmin (Or.inl hz)⟩
    rw [ht, Function.iterate_add_apply, Function.iterate_add_apply,
      bestCandidateProgram_setup p j winner value scratch hj, he]
    exact bestCandidateProgram_first p j winner value a b hz
  · by_cases hlt : p.candidateError j < value
    · refine ⟨j, p.candidateError j, bestCandidateResultScratch p j a b, ?_,
        p.minimum_take j winner value hmin (Or.inr hlt)⟩
      rw [ht, Function.iterate_add_apply, Function.iterate_add_apply,
        bestCandidateProgram_setup p j winner value scratch hj, he]
      exact bestCandidateProgram_take p j winner value a b hz hlt
    · refine ⟨winner, value, bestCandidateResultScratch p j a b, ?_,
        p.minimum_keep j winner value hmin hz hlt⟩
      rw [ht, Function.iterate_add_apply, Function.iterate_add_apply,
        bestCandidateProgram_setup p j winner value scratch hj, he]
      exact bestCandidateProgram_keep p j winner value a b hz hlt

theorem bestCandidateProgram_iterations (p : BestCandidateData) (value : ℝ)
    (scratch : BestCandidateScratch) (j : ℕ) (hj : j ≤ p.count) :
    ∃ winner : ℕ, ∃ error : ℝ, ∃ result : BestCandidateScratch,
      (ordinaryStep bestCandidateProgram)^[bestCandidateIterationTime p * j]
        (bestCandidateLoopState p 0 0 value scratch) =
          bestCandidateLoopState p j winner error result ∧ p.MinimumSoFar j winner error := by
  induction j with
  | zero => exact ⟨0, value, scratch, rfl, Or.inl rfl⟩
  | succ j ih =>
      obtain ⟨winner, error, middle, hm, hmin⟩ := ih (by omega)
      obtain ⟨winner', error', result, hr, hmin'⟩ :=
        bestCandidateProgram_iteration p j winner error middle (by omega) hmin
      refine ⟨winner', error', result, ?_, hmin'⟩
      rw [Nat.mul_succ, Nat.add_comm (bestCandidateIterationTime p * j),
        Function.iterate_add_apply, hm]
      exact hr

def bestCandidateFinalState (p : BestCandidateData) (winner : ℕ) (error : ℝ)
    (scratch : BestCandidateScratch) : State bestCandidateProgram :=
  { bestCandidateLoopState p p.count winner error scratch with
    label := 25
    status := .halted (p.candidateBase winner) }

theorem bestCandidateProgram_exit (p : BestCandidateData) (winner : ℕ) (error : ℝ)
    (scratch : BestCandidateScratch) :
    (ordinaryStep bestCandidateProgram)^[2]
      (bestCandidateLoopState p p.count winner error scratch) =
        bestCandidateFinalState p winner error scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Function.iterate_succ_apply', ordinaryStep,
    bestCandidateProgram, bestCandidateLoopState, bestCandidateFinalState, bestCandidateState]

theorem bestCandidateProgram_trace_result (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace) :
    ∃ winner < p.count, ∃ error : ℝ, ∃ result : BestCandidateScratch,
      trace.state (bestCandidateTime p) = bestCandidateFinalState p winner error result ∧
      error = p.candidateError winner ∧ ∀ i < p.count, error ≤ p.candidateError i := by
  obtain ⟨winner, error, result, hr, hmin⟩ := bestCandidateProgram_iterations p value scratch
    p.count le_rfl
  obtain ⟨hw, he, hleast⟩ := hmin.resolve_left (by omega)
  refine ⟨winner, hw, error, result, ?_, he, hleast⟩
  have htime : bestCandidateTime p = 2 + (bestCandidateIterationTime p * p.count + 2) := by
    unfold bestCandidateTime
    omega
  rw [legalTrace_scalar_prefix ht _ (fun _ _ _ => bestCandidateProgram_scalar _),
    htime, Function.iterate_add_apply, Function.iterate_add_apply, bestCandidateProgram_initial, hr]
  exact bestCandidateProgram_exit p winner error result

theorem bestCandidateTime_le_polynomial (p : BestCandidateData) :
    bestCandidateTime p ≤ 50 * (p.count + p.entries + 1)^2 := by
  let s := p.count + p.entries + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : p.count ≤ s := by dsimp [s]; omega
  have hn : 9 * p.entries + 15 ≤ 15 * s := by dsimp [s]; omega
  have hs2 : 1 ≤ s * s := by simpa only [Nat.one_mul] using Nat.mul_le_mul hs hs
  have hm : (9 * p.entries + 15) * p.count ≤ 15 * (s * s) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hn hk
  change (9 * p.entries + 15) * p.count + 4 ≤ 50 * s ^ 2
  rw [pow_two]
  omega

theorem bestCandidateProgram_run (p : BestCandidateData) (hp : 0 < p.count)
    (value : ℝ) (scratch : BestCandidateScratch) (trace : Trace bestCandidateProgram)
    (ht : LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace) :
    ∃ winner < p.count,
      (trace.state (bestCandidateTime p)).status = .halted (p.store + winner * p.entries) ∧
      (trace.state (bestCandidateTime p)).natural 5 = winner ∧
      (trace.state (bestCandidateTime p)).natural 6 = p.store + winner * p.entries ∧
      (trace.state (bestCandidateTime p)).real 3 = p.candidateError winner ∧
      (∀ i < p.count, p.candidateError winner ≤ p.candidateError i) ∧
      (trace.state (bestCandidateTime p)).memory = p.memory ∧
      CostThrough bestCandidateProgram trace (bestCandidateTime p) ≤
        50 * (p.count + p.entries + 1)^2 := by
  obtain ⟨winner, hw, error, result, hr, he, hmin⟩ :=
    bestCandidateProgram_trace_result p hp value scratch trace ht
  have hc := costThrough_le_scalar ht bestCandidateProgram_scalar (bestCandidateTime p)
  refine ⟨winner, hw, ?_, ?_, ?_, ?_, ?_, ?_, hc.trans (bestCandidateTime_le_polynomial p)⟩
  · rw [hr]
    rfl
  · rw [hr]
    rfl
  · rw [hr]
    rfl
  · rw [hr]
    exact he
  · rwa [he] at hmin
  · rw [hr]
    rfl

theorem bestCandidateProgram_exists_trace (p : BestCandidateData) (value : ℝ)
    (scratch : BestCandidateScratch) :
    ∃ trace, LegalTrace bestCandidateProgram (bestCandidateStart p value scratch) trace :=
  exists_legalTrace _ _

#assert_trust kernel bestCandidateProgram_trace_result
#assert_trust kernel bestCandidateProgram_run
#assert_trust kernel bestCandidateTime_le_polynomial
#assert_trust kernel bestCandidateProgram_exists_trace
#print axioms bestCandidateProgram_run
#print axioms bestCandidateProgram_exists_trace
end NLA.Proofs.TR04
