import NLA.Proofs.TR04.MachineTTHeaderCalls

/-! Actual trace composition for the caller's first mode/suffix/rank reads.
Only a finite explicitly listed scratch set is changed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout

private theorem ttInitTrace_naturals : ttProgram.extraNatRegisters=127 := rfl

def TTInitKept (j : Fin 128) : Prop :=
  j≠1 ∧ j≠2 ∧ j≠3 ∧ j≠80 ∧ j≠81 ∧ j≠82 ∧ j≠86 ∧ j≠97 ∧ j≠105 ∧ j≠106 ∧ j≠123

def TTInitPreserves (s t : State ttProgram) : Prop :=
  t.memory=s.memory ∧ ∀ j : Fin 128,TTInitKept j → t.natural j=s.natural j

theorem ttInitPreserves_trans {s t u : State ttProgram}
    (h : TTInitPreserves s t) (k : TTInitPreserves t u) : TTInitPreserves s u :=
  ⟨k.1.trans h.1,fun j hj => (k.2 j hj).trans (h.2 j hj)⟩

theorem ttInitPreserves_allocation {s t : State ttProgram} {L : Layout}
    (h : TTInitPreserves s t) (hs : TTAllocationRegisters L s) : TTAllocationRegisters L t := by
  constructor
  all_goals first
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.order
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.entries
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.square
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.input
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.firstU
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.firstSigma
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.firstV
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.childSigma
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.childV
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.frames
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.metadata
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.workA
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.workB
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.store
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.four
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.one
    | exact (h.2 _ (by unfold TTInitKept;decide)).trans hs.zero

theorem ttModeSuffix_preserves (s : State ttProgram) : TTInitPreserves s (ttModeSuffixEntry s) := by
  refine ⟨rfl,?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h80,h81,h82,h86,h97,h105,h106,h123⟩
  simp only [ttModeSuffixEntry,Function.update_of_ne h97,Function.update_of_ne h3,
    Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h81]

theorem ttColsRank_preserves (s : State ttProgram) : TTInitPreserves s (ttColsRankEntry s) := by
  refine ⟨rfl,?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h80,h81,h82,h86,h97,h105,h106,h123⟩
  simp only [ttColsRankEntry,Function.update_of_ne h97,Function.update_of_ne h3,
    Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h82]

theorem ttFirstRank_preserves (s : State ttProgram) : TTInitPreserves s (ttFirstRankEnd s) := by
  refine ⟨rfl,?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h80,h81,h82,h86,h97,h105,h106,h123⟩
  simp only [ttFirstRankEnd,ttFirstMinCapColsEnd,ttFirstMinCapRowsEnd,ttFirstMinRowsEnd,
    Function.update_of_ne h106,Function.update_of_ne h86,Function.update_of_ne h105,
    Function.update_of_ne h80]

theorem ttHeaderDispatch_preserves (s : State ttProgram) (k : Fin 11) :
    TTInitPreserves s (ttHeaderDispatchEnd s k) := by
  refine ⟨rfl,?_⟩
  intro j hj
  exact Function.update_of_ne hj.2.2.2.2.2.2.2.2.2.2 _ _

theorem ttHeader_preserves_of_outside {s t : State ttProgram}
    (hm : t.memory=s.memory) (hd : t.natural 0=s.natural 0)
    (hn : ∀ j : Fin 128,4≤j.val → t.natural j=s.natural j) : TTInitPreserves s t := by
  refine ⟨hm,?_⟩
  intro j hj
  by_cases h : 4≤j.val
  · exact hn j h
  · have he : j=0 := by
      have h1 : j.val≠1 := fun hh => hj.1 (Fin.ext hh)
      have h2 : j.val≠2 := fun hh => hj.2.1 (Fin.ext hh)
      have h3 : j.val≠3 := fun hh => hj.2.2.1 (Fin.ext hh)
      apply Fin.ext
      change j.val=0
      omega
    simpa only [he] using hd

theorem ttScalar_finish_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset n : ℕ) (t : State ttProgram)
    (he : (ordinaryStep ttProgram)^[n] (trace.state offset)=t) (hr : t.status=.running) :
    trace.state (offset+n)=t ∧ CostThrough ttProgram trace (offset+n)≤
      CostThrough ttProgram trace offset+n := by
  have hrun : ((ordinaryStep ttProgram)^[n] (trace.state offset)).status=.running := by
    rw [he];exact hr
  obtain ⟨hs,hc⟩ := trace_scalar_block_at ht offset n
    (fun k hk _ => ttOrdinary_nosvd_prefix_of_running _ _ hrun k hk)
  exact ⟨hs.trans he,hc⟩

theorem ttFirstRank_fields (s : State ttProgram) :
    (ttFirstRankEnd s).label=167 ∧
    (ttFirstRankEnd s).natural 80=s.natural 2 ∧
    (ttFirstRankEnd s).natural 105=min (s.natural 81) (s.natural 82) ∧
    (ttFirstRankEnd s).natural 106=min (s.natural 2) (min (s.natural 81) (s.natural 82)) ∧
    (ttFirstRankEnd s).natural 81=s.natural 81 ∧
    (ttFirstRankEnd s).natural 82=s.natural 82 := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    Fin.ext_iff,ttInitTrace_naturals,Function.update_apply,ttFirstRankEnd,ttFirstMinCapColsEnd,
    ttFirstMinCapRowsEnd,ttFirstMinRowsEnd,min_assoc]

theorem ttFirstRank_run_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=157) (hs : (trace.state offset).status=.running) :
    ∃ n : ℕ,n≤10 ∧ trace.state (offset+n)=ttFirstRankEnd (trace.state offset) ∧
      TTInitPreserves (trace.state offset) (trace.state (offset+n)) ∧
      CostThrough ttProgram trace (offset+n)≤CostThrough ttProgram trace offset+10 := by
  obtain ⟨n,hn,he⟩ := ttFirstRank_steps (trace.state offset) hl hs
  obtain ⟨hv,hc⟩ := ttScalar_finish_at ht offset n _ he hs
  refine ⟨n,hn,hv,?_,by omega⟩
  rw [hv]
  exact ttFirstRank_preserves _

theorem ttModeSuffix_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (values : ℕ → ℕ)
    (hl : (trace.state offset).label=144) (hs : (trace.state offset).status=.running)
    (hone : (trace.state offset).natural 126=1) (hd : 1≤(trace.state offset).natural 0)
    (hm : ∀ j,1≤j → j<(trace.state offset).natural 0 →
      (trace.state offset).memory j=(values j : ℝ)) :
    ∃ last : ℕ,∃ reals : Fin 2 → ℝ,
      let time := offset+6+headerRangeTime values 1 ((trace.state offset).natural 0)
      ttHeaderEmbedding.Relates (headerRangeReturnState (trace.state offset).memory
        ((trace.state offset).natural 0) 1 values last reals) (trace.state time) ∧
      TTInitPreserves (trace.state offset) (trace.state time) ∧
      (trace.state time).natural 81=(trace.state offset).natural 2 ∧
      (trace.state time).natural 97=2 ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+6+
        headerRangeTime values 1 ((trace.state offset).natural 0) := by
  let s := trace.state offset
  obtain ⟨hv,hc⟩ := ttScalar_finish_at ht offset 6 (ttModeSuffixEntry s)
    (ttModeSuffix_steps s hl hs hone) hs
  have he : ttHeaderEmbedding.Relates
      (headerRangeEntryState s.memory (s.natural 0) 1 values 0
        (fun i => s.real (ttHeaderEmbedding.reals i))) (trace.state (offset+6)) := by
    rw [hv]
    exact ttModeSuffix_relates s values hs
  obtain ⟨last,reals,hr,hn,hcost⟩ := ttHeaderRange_full_at ht (offset+6)
    s.memory (s.natural 0) 1 values hd hm 0
    (fun i => s.real (ttHeaderEmbedding.reals i)) he
  have hp : TTInitPreserves (trace.state (offset+6))
      (trace.state (offset+6+headerRangeTime values 1 (s.natural 0))) :=
    ttHeader_preserves_of_outside (hr.memory.trans he.memory.symm)
      ((hr.natural_apply 0).trans (he.natural_apply 0).symm) hn
  have hp' : TTInitPreserves s (trace.state (offset+6)) := by
    rw [hv]
    exact ttModeSuffix_preserves s
  refine ⟨last,reals,hr,ttInitPreserves_trans hp' hp,?_,?_,?_⟩
  · rw [hn 81 (by decide),hv]
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttInitTrace_naturals,Function.update_apply,ttModeSuffixEntry,s]
  · rw [hn 97 (by decide),hv]
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttInitTrace_naturals,Function.update_apply,ttModeSuffixEntry,s]

  · dsimp [s] at hcost
    omega

theorem ttColsRank_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset value : ℕ)
    (hl : (trace.state offset).label=150) (hs : (trace.state offset).status=.running)
    (hm : (trace.state offset).memory ((trace.state offset).natural 0)=(value : ℝ)) :
    let time := offset+7+(3*value+5)
    ttHeaderEmbedding.Relates (headerSingleReturnState (trace.state offset).memory
      ((trace.state offset).natural 0) value) (trace.state time) ∧
    TTInitPreserves (trace.state offset) (trace.state time) ∧
    (trace.state time).natural 81=(trace.state offset).natural 81 ∧
    (trace.state time).natural 82=(trace.state offset).natural 2 ∧
    (trace.state time).natural 97=3 ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+7+(3*value+5) := by
  let s := trace.state offset
  obtain ⟨hv,hc⟩ := ttScalar_finish_at ht offset 7 (ttColsRankEntry s)
    (ttColsRank_steps s hl hs) hs
  have he : ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value (s.real 1))
      (trace.state (offset+7)) := by
    rw [hv]
    exact ttColsRank_relates s value hm hs
  obtain ⟨hr,hn,hcost⟩ := ttHeaderSingle_full_at ht (offset+7) s.memory (s.natural 0) value
    (s.real 1) he
  have hp : TTInitPreserves (trace.state (offset+7)) (trace.state (offset+7+(3*value+5))) :=
    ttHeader_preserves_of_outside (hr.memory.trans he.memory.symm)
      ((hr.natural_apply 0).trans (he.natural_apply 0).symm) hn
  have hp' : TTInitPreserves s (trace.state (offset+7)) := by
    rw [hv]
    exact ttColsRank_preserves s
  refine ⟨hr,ttInitPreserves_trans hp' hp,?_,?_,?_,?_⟩
  · rw [hn 81 (by decide),hv]
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttInitTrace_naturals,Function.update_apply,ttColsRankEntry,s]
  · rw [hn 82 (by decide),hv]
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttInitTrace_naturals,Function.update_apply,ttColsRankEntry,s]
  · rw [hn 97 (by decide),hv]
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttInitTrace_naturals,Function.update_apply,ttColsRankEntry,s]

  · omega

theorem ttHeaderDispatch_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 11)
    (hl : (trace.state offset).label=10) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=k.val) :
    let time := offset+(2*k.val+3)
    (trace.state time).label=ttHeaderHandler k ∧
    (trace.state time).status=.running ∧
    TTInitPreserves (trace.state offset) (trace.state time) ∧
    (∀ j : Fin 128,j≠123 → (trace.state time).natural j=(trace.state offset).natural j) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+(2*k.val+3) := by
  obtain ⟨he,hc⟩ := ttHeaderDispatch_run_at ht offset k hl hs htag
  refine ⟨?_,?_,?_,?_,hc⟩
  · rw [he];rfl
  · rw [he];exact hs
  · rw [he];exact ttHeaderDispatch_preserves _ _
  · intro j hj
    rw [he]
    exact Function.update_of_ne hj _ _

#assert_trust kernel ttHeaderDispatch_call_at
#print axioms ttHeaderDispatch_call_at
#assert_trust kernel ttModeSuffix_call_at
#assert_trust kernel ttColsRank_call_at
#print axioms ttModeSuffix_call_at
#print axioms ttColsRank_call_at
#assert_trust kernel ttInitPreserves_trans
#assert_trust kernel ttInitPreserves_allocation
#assert_trust kernel ttModeSuffix_preserves
#assert_trust kernel ttColsRank_preserves
#assert_trust kernel ttFirstRank_preserves
#assert_trust kernel ttHeaderDispatch_preserves
#assert_trust kernel ttHeader_preserves_of_outside
#assert_trust kernel ttScalar_finish_at
#assert_trust kernel ttFirstRank_fields
#assert_trust kernel ttFirstRank_run_at
#print axioms ttFirstRank_run_at
end NLA.Proofs.TR04
