import NLA.Proofs.TR04.MachineThresholdScanExecution

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def thresholdScanReturnState (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau scratch : ℝ) :
    State thresholdScanProgram := { thresholdScanLoopState memory P tau P.count scratch with label := 22 }

theorem thresholdScanProgram_return (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (aux : Fin 5 → ℕ) :
    ∃ v : ℝ, (ordinaryStep thresholdScanProgram)^[9 * P.count + 6]
      (thresholdScanStart memory P tau scratch aux) = thresholdScanReturnState memory P tau v := by
  obtain ⟨v, hv⟩ := thresholdScanProgram_iterations memory P tau scratch P.count le_rfl
  refine ⟨v, ?_⟩
  have hb : (ordinaryStep thresholdScanProgram)^[9 * P.count + 5]
      (thresholdScanStart memory P tau scratch aux) = thresholdScanLoopState memory P tau P.count v := by
    rw [Function.iterate_add_apply, thresholdScanProgram_initialize, hv]
  rw [Function.iterate_succ_apply', hb]
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, ordinaryStep, thresholdScanProgram,
    thresholdScanLoopState, thresholdScanReturnState]
  all_goals rfl

theorem thresholdScanProgram_trace_result (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (aux : Fin 5 → ℕ) (trace : Trace thresholdScanProgram)
    (ht : LegalTrace thresholdScanProgram (thresholdScanStart memory P tau scratch aux) trace) :
    (trace.state (9 * P.count + 7)).status = .halted P.base ∧
      (trace.state (9 * P.count + 7)).natural 5 = thresholdAboveCount memory P tau P.count ∧
      (trace.state (9 * P.count + 7)).natural 6 = thresholdTiedCount memory P tau P.count ∧
      (trace.state (9 * P.count + 7)).natural 7 = thresholdTakeCount memory P tau P.count ∧
      (trace.state (9 * P.count + 7)).real 0 = tau ∧
      (trace.state (9 * P.count + 7)).memory = memory ∧
      CostThrough thresholdScanProgram trace (9 * P.count + 7) ≤ 9 * P.count + 7 := by
  obtain ⟨v, hv⟩ := thresholdScanProgram_return memory P tau scratch aux
  have hs : trace.state (9 * P.count + 7) =
      ordinaryStep thresholdScanProgram (thresholdScanReturnState memory P tau v) := by
    rw [legalTrace_scalar_prefix ht _ (fun _ _ _ => thresholdScanProgram_scalar _),
      Function.iterate_succ_apply', hv]
  rw [hs]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, costThrough_le_scalar ht thresholdScanProgram_scalar _⟩

theorem RoutineEmbedding.thresholdScan_run {Q : Program} (E : RoutineEmbedding thresholdScanProgram Q)
    (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau scratch : ℝ) (aux : Fin 5 → ℕ)
    {start : State Q} {trace : Trace Q}
    (hs : E.Relates (thresholdScanStart memory P tau scratch aux) start) (ht : LegalTrace Q start trace) :
    (∃ v : ℝ, E.Relates (thresholdScanReturnState memory P tau v) (trace.state (9 * P.count + 6))) ∧
      CostThrough Q trace (9 * P.count + 6) ≤ 9 * P.count + 6 := by
  obtain ⟨v, hv⟩ := thresholdScanProgram_return memory P tau scratch aux
  have hrun : ((ordinaryStep thresholdScanProgram)^[9 * P.count + 6]
      (thresholdScanStart memory P tau scratch aux)).status = .running := by rw [hv]; rfl
  have hno := ordinary_nohalt_prefix_of_running _ _ hrun
  have hscalar : ∀ k < 9 * P.count + 6, instructionIsSVD (thresholdScanProgram.code
      ((ordinaryStep thresholdScanProgram)^[k] (thresholdScanStart memory P tau scratch aux)).label) = false :=
    fun _ _ => thresholdScanProgram_scalar _
  refine ⟨⟨v, ?_⟩, E.scalar_trace_cost_le _ hs ht _ hno hscalar⟩
  have hr := E.scalar_trace_prefix _ hs ht _ hno hscalar
  rwa [hv] at hr

theorem RoutineEmbedding.thresholdScan_run_at {Q : Program} (E : RoutineEmbedding thresholdScanProgram Q)
    (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau scratch : ℝ) (aux : Fin 5 → ℕ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (thresholdScanStart memory P tau scratch aux) (trace.state offset))
    (ht : LegalTrace Q start trace) :
    ∃ v : ℝ, E.Relates (thresholdScanReturnState memory P tau v)
      (trace.state (offset + (9 * P.count + 6))) ∧
      CostThrough Q trace (offset + (9 * P.count + 6)) ≤ CostThrough Q trace offset + (9 * P.count + 6) := by
  obtain ⟨⟨v, hr⟩, hc⟩ := E.thresholdScan_run memory P tau scratch aux hs (legalTrace_shift ht offset)
  exact ⟨v, hr, costThrough_compose_le le_rfl hc⟩

theorem RoutineEmbedding.thresholdScan_run_values {Q : Program} (E : RoutineEmbedding thresholdScanProgram Q)
    (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau scratch : ℝ) (aux : Fin 5 → ℕ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (thresholdScanStart memory P tau scratch aux) (trace.state offset))
    (ht : LegalTrace Q start trace) :
    let n := offset + (9 * P.count + 6)
    (trace.state n).label = E.labels 22 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural (E.naturals 5) = thresholdAboveCount memory P tau P.count ∧
      (trace.state n).natural (E.naturals 6) = thresholdTiedCount memory P tau P.count ∧
      (trace.state n).natural (E.naturals 7) = thresholdTakeCount memory P tau P.count ∧
      (trace.state n).real (E.reals 0) = tau ∧ (trace.state n).memory = memory ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (9 * P.count + 6) := by
  obtain ⟨v, hr, hc⟩ := E.thresholdScan_run_at memory P tau scratch aux offset hs ht
  exact ⟨hr.label, hr.status, hr.natural_apply 5, hr.natural_apply 6, hr.natural_apply 7,
    hr.real_apply 0, hr.memory, hc⟩

#assert_trust kernel thresholdScanProgram_return
#assert_trust kernel thresholdScanProgram_trace_result
#assert_trust kernel RoutineEmbedding.thresholdScan_run
#assert_trust kernel RoutineEmbedding.thresholdScan_run_at
#assert_trust kernel RoutineEmbedding.thresholdScan_run_values
#print axioms RoutineEmbedding.thresholdScan_run_values
end NLA.Proofs.TR04
