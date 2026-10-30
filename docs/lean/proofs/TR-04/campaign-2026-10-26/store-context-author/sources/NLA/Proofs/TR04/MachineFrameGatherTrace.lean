import NLA.Proofs.TR04.MachineFrameGatherRows

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def frameGatherReturnState (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (aux : Fin 5 → ℕ) (value : ℝ) : State frameGatherProgram :=
  { frameGatherOuterState memory P P.rows aux value with label := 25 }

theorem frameGatherProgram_return (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ) :
    ∃ aux' : Fin 5 → ℕ, ∃ v : ℝ,
      (ordinaryStep frameGatherProgram)^[P.rows * (11 * P.width + 7) + 4]
        (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) =
          frameGatherReturnState memory P aux' v := by
  obtain ⟨aux', v, hv⟩ := frameGatherProgram_rows memory P hP hd aux value P.rows le_rfl
  refine ⟨aux', v, ?_⟩
  have hb : (ordinaryStep frameGatherProgram)^[P.rows * (11 * P.width + 7) + 3]
      (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) =
        frameGatherOuterState memory P P.rows aux' v := by
    rw [Function.iterate_add_apply, frameGatherProgram_initialize, hv]
  rw [Function.iterate_succ_apply', hb]
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, ordinaryStep, frameGatherProgram, frameGatherOuterState,
    frameGatherReturnState]
  all_goals rfl

theorem frameGatherProgram_trace_result (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    (trace : Trace frameGatherProgram)
    (ht : LegalTrace frameGatherProgram
      (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) trace) :
    (trace.state (P.rows * (11 * P.width + 7) + 5)).status = .halted P.outputBase ∧
      (trace.state (P.rows * (11 * P.width + 7) + 5)).memory =
        frameGatherMemory memory P (P.rows * P.width) ∧
      CostThrough frameGatherProgram trace (P.rows * (11 * P.width + 7) + 5) ≤
        P.rows * (11 * P.width + 7) + 5 := by
  obtain ⟨aux', v, hv⟩ := frameGatherProgram_return memory P hP hd aux
    rowScratch widthScratch writeScratch value
  have hs : trace.state (P.rows * (11 * P.width + 7) + 5) =
      ordinaryStep frameGatherProgram (frameGatherReturnState memory P aux' v) := by
    rw [legalTrace_scalar_prefix ht _ (fun _ _ _ => frameGatherProgram_scalar _),
      Function.iterate_succ_apply', hv]
  refine ⟨?_, ?_, costThrough_le_scalar ht frameGatherProgram_scalar _⟩
  · rw [hs]
    rfl
  · rw [hs]
    rfl

/-- Any caller embedding reaches its arbitrary mapped continuation with the
actual gathered memory and an actual polynomial instruction-charge bound. -/
theorem RoutineEmbedding.frameGather_run {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q}
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) start)
    (ht : LegalTrace Q start trace) :
    (∃ aux' : Fin 5 → ℕ, ∃ v : ℝ, E.Relates (frameGatherReturnState memory P aux' v)
      (trace.state (P.rows * (11 * P.width + 7) + 4))) ∧
      CostThrough Q trace (P.rows * (11 * P.width + 7) + 4) ≤ P.rows * (11 * P.width + 7) + 4 := by
  obtain ⟨aux', v, hv⟩ := frameGatherProgram_return memory P hP hd aux
    rowScratch widthScratch writeScratch value
  have hrunning : ((ordinaryStep frameGatherProgram)^[P.rows * (11 * P.width + 7) + 4]
      (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)).status = .running := by
    rw [hv]
    rfl
  have hno := ordinary_nohalt_prefix_of_running _ _ hrunning
  have hscalar : ∀ k < P.rows * (11 * P.width + 7) + 4,
      instructionIsSVD (frameGatherProgram.code ((ordinaryStep frameGatherProgram)^[k]
        (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)).label) = false :=
    fun _ _ => frameGatherProgram_scalar _
  refine ⟨⟨aux', v, ?_⟩, E.scalar_trace_cost_le _ hs ht _ hno hscalar⟩
  have hr := E.scalar_trace_prefix _ hs ht _ hno hscalar
  rwa [hv] at hr

theorem RoutineEmbedding.frameGather_run_at {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    ∃ aux' : Fin 5 → ℕ, ∃ v : ℝ, E.Relates (frameGatherReturnState memory P aux' v)
      (trace.state (offset + (P.rows * (11 * P.width + 7) + 4))) ∧
      CostThrough Q trace (offset + (P.rows * (11 * P.width + 7) + 4)) ≤
        CostThrough Q trace offset + (P.rows * (11 * P.width + 7) + 4) := by
  obtain ⟨⟨aux', v, hr⟩, hc⟩ := E.frameGather_run memory P hP hd aux
    rowScratch widthScratch writeScratch value hs (legalTrace_shift ht offset)
  exact ⟨aux', v, hr, costThrough_compose_le le_rfl hc⟩

/-- Literal matrix-column output and complete memory preservation outside the
specified dense destination, on every actual caller trace. -/
theorem RoutineEmbedding.frameGather_run_cells {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    let n := offset + (P.rows * (11 * P.width + 7) + 4)
    (trace.state n).label = E.labels 25 ∧ (trace.state n).status = .running ∧
      (∀ i < P.rows, ∀ k < P.width,
        (trace.state n).memory (P.outputBase + i * P.width + k) =
          memory (P.inputBase + i * P.rows + P.column k)) ∧
      (∀ a, ¬ (P.outputBase ≤ a ∧ a < P.outputBase + P.rows * P.width) →
        (trace.state n).memory a = memory a) ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (P.rows * (11 * P.width + 7) + 4) := by
  obtain ⟨aux', v, hr, hc⟩ := E.frameGather_run_at memory P hP hd aux
    rowScratch widthScratch writeScratch value offset hs ht
  refine ⟨hr.label, hr.status, ?_, ?_, hc⟩
  · intro i hi k hk
    rw [hr.memory]
    change frameGatherMemory memory P (P.rows * P.width) (P.outputBase + i * P.width + k) = _
    have hq : i * P.width + k < P.rows * P.width := by
      have hb := Nat.mul_le_mul (show i + 1 ≤ P.rows by omega) (show P.width ≤ P.width from le_rfl)
      rw [Nat.add_mul, Nat.one_mul] at hb
      omega
    rw [Nat.add_assoc, frameGatherMemory_output memory P _ hq, P.sourceAddress_flat i k hk]
  · intro a ha
    rw [hr.memory]
    exact frameGatherMemory_outside memory P _ a ha

#assert_trust kernel frameGatherProgram_return
#assert_trust kernel frameGatherProgram_trace_result
#assert_trust kernel RoutineEmbedding.frameGather_run
#assert_trust kernel RoutineEmbedding.frameGather_run_at
#assert_trust kernel RoutineEmbedding.frameGather_run_cells
#print axioms RoutineEmbedding.frameGather_run_cells
end NLA.Proofs.TR04
