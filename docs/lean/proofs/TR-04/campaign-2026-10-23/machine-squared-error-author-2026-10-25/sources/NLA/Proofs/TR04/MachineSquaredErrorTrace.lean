import NLA.Proofs.TR04.MachineSquaredError

/-! The squared-error program as a literal caller block. Its local halt label
is reached before executing it, so that label may hold any caller continuation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

set_option maxHeartbeats 1000000 in
theorem squaredErrorProgram_nohalt_phase (memory : ℕ → ℝ) (baseA baseB count i : ℕ)
    (scratchA scratchB : ℝ) (hi : i < count) (j : Fin 9) :
    instructionIsHalt (squaredErrorProgram.code
      ((ordinaryStep squaredErrorProgram)^[j.val]
        (squaredErrorLoopState memory baseA baseB count i scratchA scratchB)).label) = false := by
  fin_cases j <;>
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      squaredErrorProgram, squaredErrorLoopState, instructionIsHalt, hi]

theorem squaredErrorProgram_nohalt_loop_prefix (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (scratchA scratchB : ℝ) (k : ℕ) (hk : k < 9 * count + 1) :
    instructionIsHalt (squaredErrorProgram.code
      ((ordinaryStep squaredErrorProgram)^[k]
        (squaredErrorLoopState memory baseA baseB count 0 scratchA scratchB)).label) = false := by
  have hmod : k % 9 < 9 := Nat.mod_lt _ (by omega)
  have hdecomp : k = k % 9 + 9 * (k / 9) := by omega
  by_cases hi : k / 9 < count
  · obtain ⟨a, b, hv⟩ := squaredErrorProgram_iterations memory baseA baseB count
      scratchA scratchB (k / 9) (by omega)
    rw [hdecomp, Function.iterate_add_apply, hv]
    exact squaredErrorProgram_nohalt_phase memory baseA baseB count (k / 9) a b hi ⟨k % 9, hmod⟩
  · have heq : k = 9 * count := by omega
    obtain ⟨a, b, hv⟩ := squaredErrorProgram_iterations memory baseA baseB count
      scratchA scratchB count le_rfl
    rw [heq, hv]
    rfl

theorem squaredErrorProgram_nohalt_prefix (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) (k : ℕ) (hk : k < 9 * count + 2) :
    instructionIsHalt (squaredErrorProgram.code
      ((ordinaryStep squaredErrorProgram)^[k]
        (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB)).label) = false := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Function.iterate_succ_apply, squaredErrorProgram_initialize]
    exact squaredErrorProgram_nohalt_loop_prefix memory baseA baseB count
      scratchA scratchB k (by omega)

def squaredErrorReturnState (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (scratchA scratchB : ℝ) : State squaredErrorProgram :=
  { squaredErrorLoopState memory baseA baseB count count scratchA scratchB with label := 10 }

theorem squaredErrorProgram_return (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) :
    ∃ a b : ℝ, (ordinaryStep squaredErrorProgram)^[9 * count + 2]
      (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) =
        squaredErrorReturnState memory baseA baseB count a b := by
  obtain ⟨a, b, hv⟩ := squaredErrorProgram_iterations memory baseA baseB count
    scratchA scratchB count le_rfl
  refine ⟨a, b, ?_⟩
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply,
    squaredErrorProgram_initialize, hv]
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, ordinaryStep, squaredErrorProgram,
    squaredErrorLoopState, squaredErrorReturnState]
  all_goals rfl

/-- Any literal embedding returns to its caller with the actual squared error
and all memory unchanged; no separation of the two read-only arrays is needed. -/
theorem RoutineEmbedding.squaredError_run {Q : Program}
    (E : RoutineEmbedding squaredErrorProgram Q)
    (memory : ℕ → ℝ) (baseA baseB count : ℕ) (accumulator scratchA scratchB : ℝ)
    {start : State Q} {trace : Trace Q}
    (hs : E.Relates (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) start)
    (ht : LegalTrace Q start trace) :
    (∃ a b : ℝ, E.Relates (squaredErrorReturnState memory baseA baseB count a b)
      (trace.state (9 * count + 2))) ∧
      CostThrough Q trace (9 * count + 2) ≤ 9 * count + 2 := by
  have hno := squaredErrorProgram_nohalt_prefix memory baseA baseB count accumulator scratchA scratchB
  have hscalar : ∀ k < 9 * count + 2, instructionIsSVD (squaredErrorProgram.code
      ((ordinaryStep squaredErrorProgram)^[k]
        (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB)).label) = false :=
    fun _ _ => squaredErrorProgram_scalar _
  obtain ⟨a, b, hv⟩ := squaredErrorProgram_return memory baseA baseB count accumulator scratchA scratchB
  refine ⟨⟨a, b, ?_⟩, E.scalar_trace_cost_le _ hs ht _ hno hscalar⟩
  have hr := E.scalar_trace_prefix _ hs ht _ hno hscalar
  rwa [hv] at hr

theorem RoutineEmbedding.squaredError_run_at {Q : Program}
    (E : RoutineEmbedding squaredErrorProgram Q)
    (memory : ℕ → ℝ) (baseA baseB count : ℕ) (accumulator scratchA scratchB : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    ∃ a b : ℝ, E.Relates (squaredErrorReturnState memory baseA baseB count a b)
      (trace.state (offset + (9 * count + 2))) ∧
      CostThrough Q trace (offset + (9 * count + 2)) ≤
        CostThrough Q trace offset + (9 * count + 2) := by
  obtain ⟨⟨a, b, hr⟩, hc⟩ := E.squaredError_run memory baseA baseB count accumulator scratchA scratchB
    hs (legalTrace_shift ht offset)
  exact ⟨a, b, hr, costThrough_compose_le le_rfl hc⟩

theorem RoutineEmbedding.squaredError_run_value {Q : Program}
    (E : RoutineEmbedding squaredErrorProgram Q)
    (memory : ℕ → ℝ) (baseA baseB count : ℕ) (accumulator scratchA scratchB : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    (trace.state (offset + (9 * count + 2))).label = E.labels 10 ∧
      (trace.state (offset + (9 * count + 2))).real (E.reals 0) =
        squaredErrorSum memory baseA baseB count ∧
      (trace.state (offset + (9 * count + 2))).memory = memory ∧
      (trace.state (offset + (9 * count + 2))).status = .running ∧
      CostThrough Q trace (offset + (9 * count + 2)) ≤
        CostThrough Q trace offset + (9 * count + 2) := by
  obtain ⟨a, b, hr, hc⟩ := E.squaredError_run_at memory baseA baseB count
    accumulator scratchA scratchB offset hs ht
  exact ⟨hr.label, hr.real_apply 0, hr.memory, hr.status, hc⟩

#assert_trust kernel squaredErrorProgram_nohalt_phase
#assert_trust kernel squaredErrorProgram_nohalt_loop_prefix
#assert_trust kernel squaredErrorProgram_nohalt_prefix
#assert_trust kernel squaredErrorProgram_return
#assert_trust kernel RoutineEmbedding.squaredError_run
#assert_trust kernel RoutineEmbedding.squaredError_run_at
#assert_trust kernel RoutineEmbedding.squaredError_run_value
#print axioms RoutineEmbedding.squaredError_run_value
end NLA.Proofs.TR04
