import NLA.Proofs.TR04.MachineTTInitializationScalar
import NLA.Proofs.TR04.MachineTTStartup

/-! Header-bank calls preserve every caller register outside their literal
four-register frame. Call preparations are proved from the actual scalar code. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout

theorem ttHeader_outside_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State headerProductProgram)
    (he : ttHeaderEmbedding.Relates s (trace.state offset)) (n : ℕ)
    (hr : ((ordinaryStep headerProductProgram)^[n] s).status=.running)
    (j : Fin 128) (hj : 4≤j.val) :
    (trace.state (offset+n)).natural j=(trace.state offset).natural j := by
  have hf : ∀ i,j≠ttHeaderEmbedding.naturals i := by
    intro i hi
    have hv := congrArg Fin.val hi
    have hm : (ttHeaderEmbedding.naturals i).val=i.val := by
      change 0+i.val=i.val
      omega
    rw [hm] at hv
    have := i.isLt
    change i.val<4 at this
    omega
  exact ttHeaderEmbedding.scalar_trace_natural_outside s he (legalTrace_shift ht offset) n
    (ordinary_nohalt_prefix_of_running s n hr) (fun _ _ => headerProductProgram_scalar _) j hf

theorem ttHeaderSingle_full_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (memory : ℕ → ℝ)
    (d value : ℕ) (scratch : ℝ)
    (he : ttHeaderEmbedding.Relates
      (headerProductDecodeState memory d d 1 value scratch) (trace.state offset)) :
    ttHeaderEmbedding.Relates (headerSingleReturnState memory d value)
      (trace.state (offset+(3*value+5))) ∧
    (∀ j : Fin 128,4≤j.val → (trace.state (offset+(3*value+5))).natural j=
      (trace.state offset).natural j) ∧
    CostThrough ttProgram trace (offset+(3*value+5))≤
      CostThrough ttProgram trace offset+(3*value+5) := by
  obtain ⟨hr,hc⟩ := ttHeaderEmbedding.headerSingle_run_at memory d value scratch ht offset he
  refine ⟨hr,?_,hc⟩
  intro j hj
  apply ttHeader_outside_at ht offset _ he _ _ j hj
  rw [headerSingle_return]
  rfl

theorem ttHeaderRange_full_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (memory : ℕ → ℝ)
    (d a : ℕ) (values : ℕ → ℕ) (had : a≤d)
    (hm : ∀ j,a≤j → j<d → memory j=(values j : ℝ))
    (counter : ℕ) (reals : Fin 2 → ℝ)
    (he : ttHeaderEmbedding.Relates
      (headerRangeEntryState memory d a values counter reals) (trace.state offset)) :
    ∃ last : ℕ,∃ registers : Fin 2 → ℝ,
    ttHeaderEmbedding.Relates (headerRangeReturnState memory d a values last registers)
      (trace.state (offset+headerRangeTime values a d)) ∧
    (∀ j : Fin 128,4≤j.val →
      (trace.state (offset+headerRangeTime values a d)).natural j=(trace.state offset).natural j) ∧
    CostThrough ttProgram trace (offset+headerRangeTime values a d)≤
      CostThrough ttProgram trace offset+headerRangeTime values a d := by
  obtain ⟨last,registers,hr,hc⟩ := ttHeaderEmbedding.headerRange_run_at memory d a values
    had hm counter reals ht offset he
  refine ⟨last,registers,hr,?_,hc⟩
  intro j hj
  apply ttHeader_outside_at ht offset _ he _ _ j hj
  obtain ⟨last',registers',hv⟩ := headerRange_return memory d a values had hm counter reals
  rw [hv]
  rfl

theorem ttAllocation_transfer {L : Layout} {s t : State ttProgram}
    (hs : TTAllocationRegisters L s)
    (hd : t.natural 0=s.natural 0)
    (hn : ∀ j : Fin 128,4≤j.val → t.natural j=s.natural j) : TTAllocationRegisters L t := by
  constructor
  · exact hd.trans hs.order
  all_goals first
    | exact (hn _ (by decide)).trans hs.entries
    | exact (hn _ (by decide)).trans hs.square
    | exact (hn _ (by decide)).trans hs.input
    | exact (hn _ (by decide)).trans hs.firstU
    | exact (hn _ (by decide)).trans hs.firstSigma
    | exact (hn _ (by decide)).trans hs.firstV
    | exact (hn _ (by decide)).trans hs.childSigma
    | exact (hn _ (by decide)).trans hs.childV
    | exact (hn _ (by decide)).trans hs.frames
    | exact (hn _ (by decide)).trans hs.metadata
    | exact (hn _ (by decide)).trans hs.workA
    | exact (hn _ (by decide)).trans hs.workB
    | exact (hn _ (by decide)).trans hs.store
    | exact (hn _ (by decide)).trans hs.four
    | exact (hn _ (by decide)).trans hs.one
    | exact (hn _ (by decide)).trans hs.zero

theorem ttModeSuffix_relates (s : State ttProgram) (values : ℕ → ℕ)
    (hs : s.status=.running) :
    ttHeaderEmbedding.Relates
      (headerRangeEntryState s.memory (s.natural 0) 1 values 0
        (fun i => s.real (ttHeaderEmbedding.reals i))) (ttModeSuffixEntry s) := by
  constructor
  · rfl
  · rfl
  · rw [headerRange_entry_eq]
    funext i
    fin_cases i <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Function.update_apply,Fin.ext_iff,ttModeSuffixEntry,
      ttHeaderEmbedding,ttHeaderEmbeddingStage6,ttHeaderEmbeddingStage5,
      ttHeaderEmbeddingStage4,ttHeaderEmbeddingStage3,ttHeaderEmbeddingStage2,
      ttHeaderEmbeddingStage1,RoutineEmbedding.throughInstalledBank,installedBankEmbedding,
      ttHeaderRegisters,offsetBankRegisters,Function.comp_apply,headerProductProgram,
      ttControllerProgram]
  · rfl
  · exact hs

theorem ttColsRank_relates (s : State ttProgram) (value : ℕ)
    (hm : s.memory (s.natural 0)=(value : ℝ)) (hs : s.status=.running) :
    ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value (s.real 1))
      (ttColsRankEntry s) := by
  constructor
  · rfl
  · funext i
    fin_cases i <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Function.update_apply,Fin.ext_iff,ttColsRankEntry,
      headerProductDecodeState,ttHeaderEmbedding,ttHeaderEmbeddingStage6,ttHeaderEmbeddingStage5,
      ttHeaderEmbeddingStage4,ttHeaderEmbeddingStage3,ttHeaderEmbeddingStage2,
      ttHeaderEmbeddingStage1,RoutineEmbedding.throughInstalledBank,installedBankEmbedding,
      ttHeaderRegisters,offsetBankRegisters,Function.comp_apply,headerProductProgram,
      ttControllerProgram,hm]
  · funext i
    fin_cases i <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Function.update_apply,Fin.ext_iff,ttColsRankEntry,
      headerProductDecodeState,ttHeaderEmbedding,ttHeaderEmbeddingStage6,ttHeaderEmbeddingStage5,
      ttHeaderEmbeddingStage4,ttHeaderEmbeddingStage3,ttHeaderEmbeddingStage2,
      ttHeaderEmbeddingStage1,RoutineEmbedding.throughInstalledBank,installedBankEmbedding,
      ttHeaderRegisters,offsetBankRegisters,Function.comp_apply,headerProductProgram,
      ttControllerProgram]
  · rfl
  · exact hs

#assert_trust kernel ttHeader_outside_at
#assert_trust kernel ttHeaderSingle_full_at
#assert_trust kernel ttHeaderRange_full_at
#assert_trust kernel ttAllocation_transfer
#assert_trust kernel ttModeSuffix_relates
#assert_trust kernel ttColsRank_relates
#print axioms ttHeaderSingle_full_at
#print axioms ttHeaderRange_full_at
#print axioms ttModeSuffix_relates
#print axioms ttColsRank_relates
end NLA.Proofs.TR04
